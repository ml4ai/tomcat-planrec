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
          double eps,
          std::mt19937_64& g) {
    std::uniform_real_distribution<> dis(0.0,1.0);
    int original = v;
    while (!t[v].successors.empty()) {
      if (t[v].deadend) {
        return v;
      }
      double e = dis(g);
      if (e > eps) {
        std::vector<int> r_maxes = {};
        double r_max = -std::numeric_limits<double>::infinity();
        for (auto const &w : t[v].successors) {
          if (!t[w].deadend) {
            if (t[w].sims == 0) {
              return w;
            }
            double s = t[w].mean;
            if (s >= r_max) {
              if (s > r_max) {
                r_max = s;
                r_maxes.clear();
                r_maxes.push_back(w);
              }
              else {
                r_maxes.push_back(w);
              }
            }
          }
        }
        if (r_maxes.empty()) {
          t[v].deadend = true;
          v = original;
          continue;
        }
        std::vector<int> v_maxes = {};
        v_maxes.push_back(r_maxes.front());
        int v_max = t[v_maxes.back()].sims;
        for (auto const &w : r_maxes) {
          int s = t[w].sims;
          if (s >= v_max) {
            if (s > v_max) {
              v_max = s;
              v_maxes.clear();
              v_maxes.push_back(w);
            }
            else {
              v_maxes.push_back(w);
            }
          }
        }
        v = *select_randomly(v_maxes.begin(), v_maxes.end(), g);
      }
      else {
        bool all_deadends = true;
        for (auto const &w : t[v].successors) {
          if (!t[w].deadend) {
            if (t[w].sims == 0) {
              return w;
            }
            all_deadends = false;
          }
        }
        if (all_deadends) {
          t[v].deadend = true;
          v = original;
          continue;
        }
        v = *select_randomly(t[v].successors.begin(), t[v].successors.end(), g);
      }
    }
    return v;
}

void backprop(pTree& t, int n, double r) {
  do {
    if (t[n].successors.empty()) {
      t[n].mean = r;
      t[n].sims++;
    }
    else {
      t[n].mean = (r + t[n].sims*t[n].mean)/(t[n].sims + 1);
      t[n].sims++;
    }
    n = t[n].pred;
  }
  while (n != -1);
  return;
}

double
simulation(int horizon,
           std::vector<std::string>& plan,
           KnowledgeBase state,
           TaskGraph tasks,
           DomainDef& domain,
           std::mt19937_64& g,
           int h = 0) {
  if (tasks.empty() || h >= horizon) {
    return domain.score(state,plan);
  }
  h++;
  for (auto &[i,gt] : tasks.GTs) {
    if (gt.incoming.empty()) {
      if (domain.actions.contains(gt.head)) {
        auto act = domain.actions.at(gt.head).apply(state,gt.args);
        if (!act.second.empty()) {
          std::shuffle(act.second.begin(),act.second.end(),g);
          auto gtasks = tasks;
          gtasks.remove_node(i);
          for (auto &ns : act.second) {
            ns.update_state();
            auto gplan = plan;
            gplan.push_back(act.first+"_"+std::to_string(i));
            double rs = simulation(horizon,gplan,ns,gtasks,domain,g,h);
            if (rs > -1.0) {
              return rs;
            }
          }
        }
        else {
          return -1.0;
        }
      }
      else if (domain.methods.contains(gt.head)) {
        auto task_methods = domain.methods[gt.head];
        std::shuffle(task_methods.begin(),task_methods.end(),g);
        bool not_applicable = true;
        for (auto &m : task_methods) {
          auto all_gts = m.apply(state,gt.args,tasks,i);
          if (!all_gts.empty()) {
            not_applicable = false;
            std::shuffle(all_gts.begin(),all_gts.end(),g);
            for (auto &gts : all_gts) {
              double rs = simulation(horizon,plan,state,gts.second,domain,g,h);
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
        message += gt.head;
        message += " during simulation!";
        throw std::logic_error(message);
      }
    }
  }
  return -1.0;
}

int expansion(pTree& t,
              int n,
              DomainDef& domain,
              std::mt19937_64& g) {
    std::vector<int> gts; 
    for (auto const& [id,gt] : t[n].tasks.GTs) {
      if (gt.incoming.empty()) {
        gts.push_back(id);
      }
    }
    int tid = *select_randomly(gts.begin(), gts.end(), g); 
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

int
seek_planMCTS(pTree& t,
              TaskTree& tasktree,
                 int v,
                 DomainDef& domain,
                 int R,
                 int plan_size,
                 double eps,
                 int successes,
                 double prob,
                 std::mt19937_64& g) {

  std::negative_binomial_distribution<int> nbd(successes,prob);
  int prev_v;
  while (!t[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    int w = m.size();
    m[w] = n_node;
    int hzn = nbd(g);
    for (int i = 0; i < R; i++) {
      int n = selection(m,w,eps,g);
      if (m[n].tasks.empty()) {
          backprop(m,n,domain.score(m[n].state,m[n].plan));
      }
      else {
        if (m[n].sims == 0) {
          auto r = simulation(hzn,
                               m[n].plan,
                               m[n].state, 
                               m[n].tasks, 
                               domain,
                               g);
          if (r == -1.0) {
            m[n].deadend = true;
          }
          backprop(m,n,r);
        }
        else {
          int n_p = expansion(m,n,domain,g);
          auto r = simulation(hzn,
                               m[n_p].plan,
                               m[n_p].state, 
                               m[n_p].tasks, 
                               domain,
                               g);
          if (r == -1.0) {
            m[n_p].deadend = true;
          }
          backprop(m,n_p,r);
        }
      }
    }
    if (m[w].successors.empty()) {
      continue;
    }
    std::vector<int> arg_maxes = {};
    double max = -std::numeric_limits<double>::infinity();
    for (auto const &s : m[w].successors) {
      if (!m[s].deadend) {
        double mean = m[s].mean;
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
    if (arg_maxes.empty() || max == -1.0) {
      continue;
    }
    int arg_max = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.state = m[arg_max].state;
    k.tasks = m[arg_max].tasks;
    k.plan = m[arg_max].plan;
    k.depth = t[v].depth + 1;
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
      j.state = m[arg_max].state;
      j.tasks = m[arg_max].tasks;
      j.plan = m[arg_max].plan;
      j.depth = t[v].depth + 1;
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
           double eps = 0.4,
           int successes = 19,
           double prob = 0.75,
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
    auto end = seek_planMCTS(t, tasktree, v, domain, R, plan_size, eps, successes,prob,g);
    std::cout << "Plan:";
    for (auto const& p : t[end].plan) {
      std::cout << " " << p;
    }
    std::cout << std::endl;
    return Results(t,v,end,tasktree,TID);
}
