#pragma once

#include "../util.h"
#include "../typedefs.h"
//#include "printing.h"
#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include <limits>

int
selection(pTree& t,
          int v,
          double c,
          std::mt19937_64& g) {
    int original = v;
    while (!t[v].successors.empty()) {
      if (t[v].deadend) {
        return v;
      }
      std::vector<int> maxes = {};
      double max = -std::numeric_limits<double>::infinity();
      for (auto const &w : t[v].successors) {
        if (!t[w].deadend) {
          if (t[w].sims == 0) {
            return w;
          }
          double s = (t[w].score/t[w].sims) + c*sqrt(log(t[v].sims)/t[w].sims);
          if (s >= max) {
            if (s > max) {
              max = s;
              maxes.clear();
              maxes.push_back(w);
            }
            else {
              maxes.push_back(w);
            }
          }
        }
      }
      if (maxes.empty()) {
        t[v].deadend = true;
        v = original;
        continue;
      }
      v = *select_randomly(maxes.begin(), maxes.end(), g);
    }
    return v;
}

void backprop(pTree& t, int n, double r) {
  do {
    if (t[n].successors.empty()) {
      t[n].score = r;
      t[n].sims++;
    }
    else {
      t[n].score += r;
      t[n].sims++;
    }
    n = t[n].pred;
  }
  while (n != -1);
  return;
}

double
simulation(std::vector<std::string>& plan,
           KnowledgeBase state,
           TaskGraph tasks,
           int cTask,
           int time,
           DomainDef& domain,
           std::mt19937_64& g) {
  if (tasks.empty() && cTask == -1) {
    return domain.score(state,plan);
  }
  if (cTask != -1) {
    if (domain.actions.contains(tasks[cTask].head)) {
      auto act = domain.actions.at(tasks[cTask].head).apply(state,tasks[cTask].args);
      if (!act.second.empty()) {
        std::shuffle(act.second.begin(),act.second.end(),g);
        auto gtasks = tasks;
        gtasks.remove_node(cTask);
        for (auto &ns : act.second) {
          ns.update_state();
          auto gplan = plan;
          gplan.push_back(act.first+"_"+std::to_string(cTask));
          double rs = simulation(gplan,ns,gtasks,-1,time + 1,domain,g);
          if (rs > -1.0) {
            return rs;
          }
        }
      }
      else {
        return -1.0;
      }
    }
    else if (domain.methods.contains(tasks[cTask].head)) {
      auto task_methods = domain.methods[tasks[cTask].head];
      std::shuffle(task_methods.begin(),task_methods.end(),g);
      bool not_applicable = true;
      for (auto &m : task_methods) {
        auto all_gts = m.apply(state,tasks[cTask].args,tasks,cTask);
        if (!all_gts.empty()) {
          not_applicable = false;
          std::shuffle(all_gts.begin(),all_gts.end(),g);
          for (auto &gts : all_gts) {
            double rs = simulation(plan,state,gts.second,-1,time,domain,g);
            if (rs > -1.0) {
              return rs;
            }
          }
        }
      }
      if (not_applicable) {
        return -1.0;
      }
    }
    else {
      std::string message = "Invalid task ";
      message += tasks[cTask].head;
      message += " during simulation!";
      throw std::logic_error(message);
    }
  }
  else {
    for (auto &[i,gt] : tasks.GTs) {
      if (gt.incoming.empty()) {
        double rs = simulation(plan,state,tasks,i,time,domain,g);
        if (rs > -1.0) {
          return rs;
        }
      }
    }
  }
  return -1.0;
}

int expansion(pTree& t,
              int n,
              DomainDef& domain,
              std::mt19937_64& g) {
    if (t[n].cTask != -1) {
      int tid = t[n].cTask;
      if (domain.actions.contains(t[n].tasks[tid].head)) {
        auto act = domain.actions.at(t[n].tasks[tid].head).apply(t[n].state,t[n].tasks[tid].args);
        if (!act.second.empty()) {
          std::vector<int> a;
          for (auto const& state : act.second) {
            pNode v;
            v.state = state;
            v.state.update_state();
            v.tasks = t[n].tasks;
            v.tasks.remove_node(tid);
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.time = t[n].time + 1;
            v.plan.push_back(act.first+"_"+std::to_string(tid));
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].successors.push_back(w);
            a.push_back(w);
          }
          int r = *select_randomly(a.begin(), a.end(), g);
          return r;
        }
        t[n].deadend = true;
        return n;
      }

      if (domain.methods.contains(t[n].tasks[tid].head)) {
        std::vector<int> choices;
        for (auto &m : domain.methods[t[n].tasks[tid].head]) {
          auto gts = m.apply(t[n].state,t[n].tasks[tid].args,t[n].tasks,tid);
          for (auto &g : gts) { 
            pNode v;
            v.state = t[n].state;
            v.tasks = g.second;
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.addedTIDs = g.first;
            v.prevTID = tid;
            v.time = t[n].time;
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].successors.push_back(w);
            choices.push_back(w);
          }
        }
        if (choices.empty()) {
          t[n].deadend = true;
          return n;
        }
        int r = *select_randomly(choices.begin(), choices.end(), g);
        return r;
      }
      throw std::logic_error("Invalid task during expansion!");
    }
    else {
      std::vector<int> gts;
      for (auto const& [id,gt] : t[n].tasks.GTs) {
        if (gt.incoming.empty()) {
          pNode v;
          v.cTask = id;
          v.state = t[n].state;
          v.tasks = t[n].tasks;
          v.depth = t[n].depth + 1;
          v.plan = t[n].plan;
          v.pred = n;
          int w = t.size();
          t[w] = v;
          t[n].successors.push_back(w);
          gts.push_back(w);
        }
      }
      int r = *select_randomly(gts.begin(), gts.end(), g);
      return r;
    }
    t[n].deadend = true;
    return n;
}

int
seek_planMCTS(pTree& t,
              TaskTree& tasktree,
              int v,
              DomainDef& domain,
              int R,
              int plan_size,
              double c,
              std::mt19937_64& g) {
  int stuck_counter = 10;
  while (!t[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.cTask = t[v].cTask;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    n_node.time = t[v].time;
    int w = m.size();
    m[w] = n_node;
    for (int i = 0; i < R; i++) {
      int n = selection(m,w,c,g);
      if (m[n].tasks.empty() && m[n].cTask == -1) {
          backprop(m,n,domain.score(m[n].state,m[n].plan));
      }
      else {
        if (m[n].sims == 0) {
          auto r = simulation(m[n].plan,
                              m[n].state, 
                              m[n].tasks, 
                              m[n].cTask,
                              m[n].time,
                              domain,
                              g);
          if (r == -1.0) {
            m[n].deadend = true;
            backprop(m,n,0);
          }
          else {
            backprop(m,n,r);
          }
        }
        else {
          int n_p = expansion(m,n,domain,g);
          auto r = simulation(m[n_p].plan,
                              m[n_p].state, 
                              m[n_p].tasks, 
                              m[n_p].cTask,
                              m[n_p].time,
                              domain,
                              g);
          if (r == -1.0) {
            m[n_p].deadend = true;
            backprop(m,n_p,0);
          }
          else {
            backprop(m,n_p,r);
          }
        }
      }
    }
    if (m[w].successors.empty()) {
      stuck_counter--;
      if (stuck_counter <= 0) {
        throw std::logic_error("Planner is stuck, terminating process!"); 
      }
      continue;
    }

    std::vector<int> arg_maxes = {};
    double max = -std::numeric_limits<double>::infinity();
    for (auto const &s : m[w].successors) {
      if (!m[s].deadend) {
        double mean = m[s].score/m[s].sims;
        if (mean >= max) {
          if (mean > max) {
            max = mean;
            arg_maxes.clear();
            arg_maxes.push_back(s);
          }
          else {
            arg_maxes.push_back(s); 
          }
        }
      }
    }
    if (arg_maxes.empty()) {
      stuck_counter--;
      if (stuck_counter <= 0) {
        throw std::logic_error("Planner is stuck, terminating process!");
      }
      continue;
    }
    stuck_counter = 10;

    int arg_max = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.cTask = m[arg_max].cTask;
    k.state = m[arg_max].state;
    k.tasks = m[arg_max].tasks;
    k.plan = m[arg_max].plan;
    k.depth = t[v].depth + 1;
    k.time = m[arg_max].time;
    for (auto& i : m[arg_max].addedTIDs) {
      TaskNode tasknode;
      tasknode.task = k.tasks[i].head;
      tasknode.token = k.tasks[i].to_string();
      tasknode.outgoing = k.tasks[i].outgoing;
      tasktree[i] = tasknode;
      tasktree[m[arg_max].prevTID].children.push_back(i);
    }
    k.pred = v;
    int y = t.size();
    t[y] = k;
    t[v].successors.push_back(y);
    v = y;
    if (t[v].plan.size() >= plan_size && plan_size != -1) {
      break;
    }
      
    bool plan_break = false;
    while (m[arg_max].successors.size() == 1) {
      if (m[arg_max].deadend) {
        continue;
      }
      arg_max = m[arg_max].successors.front();

      pNode j;
      j.cTask = m[arg_max].cTask;
      j.state = m[arg_max].state;
      j.tasks = m[arg_max].tasks;
      j.plan = m[arg_max].plan;
      j.depth = t[v].depth + 1;
      j.time = m[arg_max].time;
      for (auto& i : m[arg_max].addedTIDs) {
        TaskNode tasknode;
        tasknode.task = j.tasks[i].head;
        tasknode.token = j.tasks[i].to_string();
        tasknode.outgoing = j.tasks[i].outgoing;
        tasktree[i] = tasknode;
        tasktree[m[arg_max].prevTID].children.push_back(i);
      }
      j.pred = v;
      int y = t.size();
      t[y] = j;
      t[v].successors.push_back(y);
      v = y;

      if (t[v].plan.size() >= plan_size && plan_size != -1) {
        plan_break = true;
        break;
      }
    }
    if (plan_break) {
      break;
    }
  }
  std::cout << "Plan found at depth " << t[v].depth;
  std::cout << std::endl;
  std::cout << "Final State:" << std::endl;
  t[v].state.print_facts();
  std::cout << std::endl;
  return v;

}

Results 
cppMCTShop(DomainDef& domain,
           ProblemDef& problem,
           Scorer scorer,
           int R = 30,
           int plan_size = -1,
           double c = 1.4142,
           int seed = 4021) {
    domain.set_scorer(scorer);
    pTree t;
    TaskTree tasktree;
    pNode root;
    root.state = KnowledgeBase(domain.predicates,problem.objects,domain.typetree);
    for (auto const& f : problem.initF) {
      root.state.tell(f,false,false);
    }
    root.state.update_state();
    Grounded_Task init_t;
    init_t.head = problem.head;
    int TID = root.tasks.add_node(init_t);
    TaskNode tasknode;
    tasknode.task = init_t.head;
    tasknode.token = init_t.to_string();
    tasktree[TID] = tasknode;
    root.plan = {};
    root.depth = 0;
    int v = t.size();
    t[v] = root;
    static std::mt19937_64 g(seed);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    t[v].state.print_facts();
    std::cout << std::endl;
    auto end = seek_planMCTS(t, tasktree, v, domain, R, plan_size,c,g);
    std::cout << "Plan:";
    for (auto const& p : t[end].plan) {
      std::cout << "\n\t " << p;
    }
    std::cout << std::endl;
    return Results(t,v,end,tasktree,TID);
}
