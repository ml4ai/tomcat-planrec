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
#include "redis_pipeline.h"
#include "Redis_Connect.h"
#include <boost/json.hpp>
#include <chrono>

namespace json = boost::json;

bool is_subseq(std::vector<std::string> plan, std::vector<std::pair<int,std::string>> O) {
  for (int i = 0; i < plan.size(); i++) {
    if (plan[i].find(O[i].second) == std::string::npos) {
      return false;
    }
  }
  return true;
}

double
simulation_rec(std::vector<std::pair<int,std::string>>& actions,
               std::vector<std::string> plan,
               KnowledgeBase state,
               TaskGraph tasks,
               int cTask,
               DomainDef& domain,
               Reach_Map& r_map,
               std::mt19937_64& g) {
  if (!is_subseq(plan,actions)) {
    return -1.0;
  }

  if (plan.size() == actions.size() || (tasks.empty() && cTask == -1)) {
    return domain.score(state,plan);
  }


  if (cTask != -1) {
    if (domain.actions.contains(tasks[cTask].head)) {
      if (plan.size() < actions.size()) {
        if (actions[plan.size()].second.find(tasks[cTask].head) == std::string::npos) {
          return -1.0;
        }
      }
      auto act = domain.actions.at(tasks[cTask].head).apply(state,tasks[cTask].args);
      if (!act.second.empty()) {
        std::shuffle(act.second.begin(),act.second.end(),g);
        auto gtasks = tasks;
        gtasks.remove_node(cTask);
        for (auto &ns : act.second) {
          auto gplan = plan;
          gplan.push_back(act.first+"_"+std::to_string(cTask));
          if (gplan.size() < actions.size()) {
            ns.update_state(actions[gplan.size()].first);
          }
          else {
            ns.update_state();
          }
          double rs = simulation_rec(actions,gplan,ns,gtasks,-1,domain,r_map,g);
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
        bool can_reach = false;
        if (r_map.find(m.get_head()) != r_map.end() && plan.size() < actions.size()) {
          for (auto const& a : r_map[m.get_head()]) {
            if (actions[plan.size()].second.find(a) != std::string::npos) {
              can_reach = true;
            } 
          } 
        }
        else {
          can_reach = true;
        }
        if (can_reach) {
          auto all_gts = m.apply(state,tasks[cTask].args,tasks,cTask);
          if (!all_gts.empty()) {
            not_applicable = false;
            std::shuffle(all_gts.begin(),all_gts.end(),g);
            for (auto &gts : all_gts) {
              double rs = simulation_rec(actions,plan,state,gts.second,-1,domain,r_map,g);
              if (rs > -1.0) {
                return rs;
              }
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
        bool can_reach = false;
        if (r_map.find(gt.head) != r_map.end() && plan.size() < actions.size()) {
          for (auto const& a : r_map[gt.head]) {
            if (actions[plan.size()].second.find(a) != std::string::npos) {
              can_reach = true;
            }
          }
        }
        else {
          can_reach = true;
        }
        if (can_reach) {
          double rs = simulation_rec(actions,plan,state,tasks,i,domain,r_map,g);
          if (rs > -1.0) {
            return rs;
          }
        }
      }
    }
  }
  return -1.0;
}

int expansion_rec(std::vector<std::pair<int,std::string>> actions,
                  pTree& t,
                  int n,
                  DomainDef& domain,
                  Reach_Map r_map,
                  std::mt19937_64& g) {
    if (t[n].cTask != -1) {
      int tid = t[n].cTask;
      if (domain.actions.contains(t[n].tasks[tid].head)) {
        if (t[n].plan.size() < actions.size()) {
          if (actions[t[n].plan.size()].second.find(t[n].tasks[tid].head) == std::string::npos) {
            return n;
          }
        }
        auto act = domain.actions.at(t[n].tasks[tid].head).apply(t[n].state,t[n].tasks[tid].args);
        if (!act.second.empty()) {
          for (auto const& state : act.second) {
            pNode v;
            v.state = state;
            v.tasks = t[n].tasks;
            v.tasks.remove_node(tid);
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.plan.push_back(act.first+"_"+std::to_string(tid));
            if (v.plan.size() < actions.size()) {
              v.state.update_state(actions[v.plan.size()].first);
            }
            else {
              v.state.update_state();
            }
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].unexplored.push_back(w);
          }
          std::shuffle(t[n].unexplored.begin(),t[n].unexplored.end(),g);
          int r = t[n].unexplored.back();
          t[n].successors.push_back(r);
          t[n].unexplored.pop_back();
          return r;
        }
        t[n].deadend = true;
        return n;
      }

      if (domain.methods.contains(t[n].tasks[tid].head)) {
        for (auto &m : domain.methods[t[n].tasks[tid].head]) {
          bool can_reach = false;
          if (r_map.find(m.get_head()) != r_map.end() && t[n].plan.size() < actions.size()) {
            for (auto const& a : r_map[m.get_head()]) {
              if (actions[t[n].plan.size()].second.find(a) != std::string::npos) {
                can_reach = true;
              }
            }
          }
          else {
            can_reach = true;
          }
          if (can_reach) {
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
              t[n].unexplored.push_back(w);
            }
          }
        }
        if (t[n].unexplored.empty()) {
          t[n].deadend = true;
          return n;
        }
        std::shuffle(t[n].unexplored.begin(),t[n].unexplored.end(),g);
        int r = t[n].unexplored.back();
        t[n].successors.push_back(r);
        t[n].unexplored.pop_back();
        return r;
      }
      throw std::logic_error("Invalid task during expansion!");
    }
    else {
      for (auto const& [id,gt] : t[n].tasks.GTs) {
        if (gt.incoming.empty()) {
          bool can_reach = false;
          if (r_map.find(gt.head) != r_map.end() && t[n].plan.size() < actions.size()) {
            for (auto const& a : r_map[gt.head]) {
              if (actions[t[n].plan.size()].second.find(a) != std::string::npos) {
                can_reach = true;
              }
            }
          }
          else {
            can_reach = true;
          }
          if (can_reach) {
            pNode v;
            v.cTask = id;
            v.state = t[n].state;
            v.tasks = t[n].tasks;
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].unexplored.push_back(w);
          }
        }
      }
      if (!t[n].unexplored.empty()) {
        std::shuffle(t[n].unexplored.begin(),t[n].unexplored.end(),g);
        int r = t[n].unexplored.back();
        t[n].successors.push_back(r);
        t[n].unexplored.pop_back();
        return r;
      }
      else {
        t[n].deadend = true;
        return n;
      }
    }
    t[n].deadend = true;
    return n;
}

Results
seek_planrecMCTS(pTree& t,
                 TaskTree& tasktree,
                 int v,
                 DomainDef& domain,
                 Reach_Map& r_map,
                 int time_limit,
                 int r,
                 double c,
                 std::mt19937_64& g,
                 std::vector<std::pair<int,std::string>>& actions,
                 std::string const& redis_address) {
  int root = v;
  t[v].time = actions.back().first;
  pTree m;
  pNode n_node;
  n_node.cTask = t[v].cTask;
  t[v].state.update_temporal_facts(redis_address);
  t[v].state.update_state(t[v].time);
  n_node.state = t[v].state;
  n_node.tasks = t[v].tasks;
  n_node.depth = t[v].depth;
  n_node.plan = t[v].plan;
  int w = m.size();
  m[w] = n_node;
  auto start = std::chrono::high_resolution_clock::now();
  auto stop = std::chrono::high_resolution_clock::now();
  while (std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count() < time_limit) {
    int n = selection(m,w,c,g);
    if (w == n && m[n].deadend) {
      std::cout << "Warning: Deadend reached, returning current results!" << std::endl;
      break;  
    }
    if (m[n].sims == 0) {
      m[n].state.update_state(m[n].time);
      double ar = 0.0;
      bool bp = true;
      for (int j = 0; j < r; j++) {
        ar += simulation_rec(actions,
                              m[n].plan,
                              m[n].state, 
                              m[n].tasks, 
                              m[n].cTask,
                              domain,
                              r_map,
                              g);
        if (ar == -1.0) {
          m[n].deadend = true;
          backprop(m,n,-1.0,1);
          bp = false;
          break;
        }
      }
      if (bp) {
        backprop(m,n,ar,r);
      }
    }
    else {
      m[n].state.update_state(m[n].time);
      int n_p = expansion_rec(actions,m,n,domain,r_map,g);
      double ar = 0.0;
      bool bp = true;
      for (int j = 0; j < r; j++) {
        ar += simulation_rec(actions,
                              m[n_p].plan,
                              m[n_p].state, 
                              m[n_p].tasks, 
                              m[n_p].cTask,
                              domain,
                              r_map,
                              g);
        if (ar == -1.0) {
          m[n_p].deadend = true;
          backprop(m,n_p,-1.0,1);
          bp = false;
          break;
        }
      }
      if (bp) {
        backprop(m,n_p,ar,r);
      }
    }
    stop = std::chrono::high_resolution_clock::now();
  }
  while(!m[w].successors.empty()) {
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
    if (arg_maxes.empty() || max <= -1.0) {
      std::cout << "Warning: Deadend reached, returning current results!" << std::endl;
      break;
    }
    w = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.cTask = m[w].cTask;
    k.state = m[w].state;
    k.tasks = m[w].tasks;
    k.plan = m[w].plan;
    k.depth = t[v].depth + 1;
    for (auto& i : m[w].addedTIDs) {
      TaskNode tasknode;
      tasknode.task = k.tasks[i].head;
      tasknode.token = k.tasks[i].to_string();
      tasknode.outgoing = k.tasks[i].outgoing;
      tasktree[i] = tasknode;
      tasktree[m[w].prevTID].children.push_back(i);
    }
    k.pred = v;
    int y = t.size();
    t[y] = k;
    t[v].successors.push_back(y);
    v = y;
    if (actions.size() == t[v].plan.size()) {
      break;
    }
  }
  return Results(t,root,v,tasktree,0);
}

Results 
cppMCTSplanrec(DomainDef& domain,
              ProblemDef& problem,
              Reach_Map& r_map,
              Scorer scorer,
              std::vector<std::pair<int,std::string>>& actions,
              int time_limit = 1000,
              int r = 5,
              double c = 1.4,
              int seed = 4021,
              std::string const& redis_address = "") {
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
    seed++;
    return seek_planrecMCTS(t, 
                            tasktree, 
                            v, 
                            domain, 
                            r_map,
                            time_limit, 
                            r,
                            c, 
                            g,
                            actions,
                            redis_address);
}
