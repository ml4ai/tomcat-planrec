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
#include "cppMCTShop.h"

bool is_subseq(std::vector<std::string> plan, std::vector<std::string> O) {
  if (plan.size() <= O.size()) {
    for (int i = 0; i < plan.size(); i++) {
      if (plan[i].find(O[i]) == std::string::npos) {
        return false;
      }
    }
    return true;
  }
  for (int i = 0; i < O.size(); i++) {
    if (plan[i].find(O[i]) == std::string::npos) {
      return false;
    }
  }
  return true;
}

double
simulation_rec(int horizon,
               std::vector<std::string> given_plan,
               std::vector<std::string> plan,
               KnowledgeBase state,
               TaskGraph tasks,
               int cTask,
               DomainDef& domain,
               std::mt19937_64& g,
               int h = 0) {

  if (!is_subseq(plan,given_plan)) {
    return -1.0;
  }
  if ((tasks.empty() && cTask == -1) || h >= horizon) {
    return domain.score(state,plan);
  }
  h++;
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
          double rs = simulation_rec(horizon,given_plan,plan,ns,gtasks,-1,domain,g,h);
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
            double rs = simulation_rec(horizon,given_plan,plan,state,gts.second,-1,domain,g,h);
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
        double rs = simulation_rec(horizon,given_plan,plan,state,tasks,i,domain,g,h);
        if (rs > -1.0) {
          return rs;
        }
      }
    }
  }
  return -1.0;
}


int
seek_planrecMCTS(pTree& t,
                 std::vector<std::string> given_plan,
                 TaskTree& tasktree,
                 int v,
                 DomainDef& domain,
                 int R,
                 double eps,
                 int successes,
                 double prob,
                 int pred,
                 std::mt19937_64& g) {

  std::negative_binomial_distribution<int> nbd(successes,prob);
  int g_p_size = given_plan.size();
  int stuck_counter = 10;
  while (!t[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.cTask = t[v].cTask;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    int w = m.size();
    m[w] = n_node;
    int hzn = nbd(g);
    for (int i = 0; i < R; i++) {
      int n = selection(m,w,eps,g);
      int m_p_size = m[n].plan.size();
      if ((m[n].tasks.empty() && m[n].cTask == -1) || (m_p_size - g_p_size) >= pred) {
        if (is_subseq(m[n].plan,given_plan)) {
          backprop(m,n,domain.score(m[n].state,m[n].plan));
        }
        else {
          backprop(m,n,-1.0);
          m[n].deadend = true;
        }
      }
      else {
        if (m[n].sims == 0) {
          auto r = simulation_rec(hzn,
                                  given_plan,
                                  m[n].plan,
                                  m[n].state, 
                                  m[n].tasks, 
                                  m[n].cTask,
                                  domain,
                                  g);
          if (r == -1.0) {
            m[n].deadend = true;
          }
          backprop(m,n,r);
        }
        else {
          int n_p = expansion(m,n,domain,g);
          auto r = simulation_rec(hzn,
                              given_plan,
                              m[n_p].plan,
                              m[n_p].state, 
                              m[n_p].tasks, 
                              m[n_p].cTask,
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
      stuck_counter--;
      if (stuck_counter <= 0) {
        throw std::logic_error("Planner is stuck, terminating process!");
      }
      continue;
    }
    int arg_max = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.cTask = m[arg_max].cTask;
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
    int t_p_size = t[v].plan.size();
    if (t_p_size - g_p_size == pred) {
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
      t_p_size = t[v].plan.size();
      if (t_p_size - g_p_size == pred) {
        plan_break = true;
        break;
      }
    }
    if (plan_break) {
      break;
    }
  }
  return v;

}

Results 
cppMCTSplanrec(DomainDef& domain,
              ProblemDef& problem,
              std::vector<std::string> given_plan,
              Scorer scorer,
              int R = 30,
              double eps = 0.4,
              int successes = 19,
              double prob = 0.75,
              int seed = 4021,
              int pred = 0) {
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
    auto end = seek_planrecMCTS(t, 
                                given_plan,
                                tasktree, 
                                v, 
                                domain, 
                                R, 
                                eps, 
                                successes,
                                prob,
                                pred,
                                g);
    return Results(t,v,end,tasktree,TID);
}
