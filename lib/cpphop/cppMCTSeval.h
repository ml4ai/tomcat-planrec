#pragma once

#include "../util.h"
#include "../typedefs.h"
#include "cppMCTShop.h"
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

double
simulation_eval(std::vector<std::string>& plan,
                KnowledgeBase state,
                TaskGraph tasks,
                std::vector<int>& times,
                DomainDef& domain,
                std::mt19937_64& g) {
  if (tasks.empty()) {
    return domain.score(state,plan);
  }
  std::vector<int> u;
  for (auto &[i,gt] : tasks.GTs) {
    if (gt.incoming.empty()) {
      if (domain.actions.contains(tasks[i].head)) {
        u.push_back(i);
      }
      else if (domain.methods.contains(tasks[i].head)) {
        u.push_back(i);
      }
      else {
        std::string message = "Invalid task ";
        message += tasks[i].head;
        message += " during simulation!";
        throw std::logic_error(message);
      }
    }
  }
  if (u.empty()) {
    return -1.0;
  }
  std::shuffle(u.begin(),u.end(),g);

  for (auto const& cTask : u) { 
    if (domain.actions.contains(tasks[cTask].head)) {
      auto act = domain.actions.at(tasks[cTask].head).apply(state,tasks[cTask].args);
      if (!act.second.empty()) {
        auto gtasks = tasks;
        gtasks.remove_node(cTask);
        for (auto &ns : act.second) {
          auto gplan = plan;
          gplan.push_back(act.first+"_"+std::to_string(cTask));
          if (gplan.size() == times.size()) {
            ns.update_state();
            return domain.score(ns,gplan);
          }
          ns.update_state(times[gplan.size()]);
          double rs = simulation_eval(gplan,ns,gtasks,times,domain,g);
          if (rs > -1.0) {
            return rs;
          }
        }
      }
      else {
        return -1.0;
      }
    }
    else {
      auto task_methods = domain.methods[tasks[cTask].head];
      std::shuffle(task_methods.begin(),task_methods.end(),g);
      bool not_applicable = true;
      for (auto &m : task_methods) {
        auto all_gts = m.apply(state,tasks[cTask].args,tasks,cTask);
        if (!all_gts.empty()) {
          not_applicable = false;
          std::shuffle(all_gts.begin(),all_gts.end(),g);
          for (auto &gts : all_gts) {
            double rs = simulation_eval(plan,state,gts.second,times,domain,g);
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
  }
  return -1.0;
}

int expansion_eval(pTree& t,
                  int n,
                  DomainDef& domain,
                  std::vector<int>& times,
                  std::mt19937_64& g) {
    std::vector<int> u;
    for (auto const& [id,gt] : t[n].tasks.GTs) {
      if (gt.incoming.empty()) {
        if (domain.actions.contains(t[n].tasks[id].head)) {
          u.push_back(id);
        }
        else if (domain.methods.contains(t[n].tasks[id].head)) {
          u.push_back(id);
        }
        else {
          std::string message = "Invalid task ";
          message += t[n].tasks[id].head;
          message += " during simulation!";
          throw std::logic_error(message);
        }
      }
    } 
    if (u.empty()) {
      t[n].deadend = true;
      return n;
    }
    
    for (auto const& tid : u) {
      if (domain.actions.contains(t[n].tasks[tid].head)) {
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
            if (times.size() == v.plan.size()) {
              v.state.update_state();
            }
            else {
              v.state.update_state(times[v.plan.size()]);
              v.time = times[v.plan.size()];
            }
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].unexplored.push_back(w);
          }
        }
      }
      else {
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
            t[n].unexplored.push_back(w);
          }
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
    t[n].deadend = true;
    return n;
}

int
seek_evalMCTS(pTree& t,
              int v,
              DomainDef& domain,
              std::vector<int>& times,
              int time_limit,
              int r,
              double c,
              std::mt19937_64& g,
              std::string const& redis_address) {
  int stuck_counter = 10;
  t[v].time = times[0];
  while (!t[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.cTask = t[v].cTask;
    if (!redis_address.empty()) {
      t[v].state.update_temporal_facts(redis_address);
    }
    t[v].state.update_state(t[v].time);
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    n_node.time = t[v].time;
    int w = m.size();
    m[w] = n_node;
    auto start = std::chrono::high_resolution_clock::now();
    auto stop = std::chrono::high_resolution_clock::now();
    while (std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count() < time_limit) {
      int n = selection(m,w,c,g);
      if (m[n].tasks.empty() && m[n].cTask == -1) {
          backprop(m,n,domain.score(m[n].state,m[n].plan),1);
      }
      else if (m[n].plan.size() >= times.size()) {
        backprop(m,n,domain.score(m[n].state,m[n].plan),1);
      }
      else {
        if (m[n].sims == 0) {
          m[n].state.update_state(m[n].time);
          double ar = 0.0;
          bool bp = true;
          for (int j = 0; j < r; j++) {
            ar += simulation_eval(m[n].plan,
                                  m[n].state, 
                                  m[n].tasks, 
                                  times,
                                  domain,
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
          int n_p = expansion_eval(m,n,domain,times,g);
          m[n_p].state.update_state(m[n_p].time);
          double ar = 0.0;
          bool bp = true;
          for (int j = 0; j < r; j++) {
            ar += simulation_eval(m[n_p].plan,
                                  m[n_p].state, 
                                  m[n_p].tasks, 
                                  times,
                                  domain,
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
      }
      stop = std::chrono::high_resolution_clock::now();
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
      int u = t[v].pred;
      for (std::vector<int>::iterator it = t[u].successors.begin(); it != t[u].successors.end();) {
        if (*it == v) {
          t[u].successors.erase(it);
          break;
        }
      }
      t.erase(v);
      v = u;
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
    k.pred = v;
    int y = t.size();
    t[y] = k;
    t[v].successors.push_back(y);
    v = y;
    if (t[v].plan.size() >= times.size()) {
      break;
    }
  }
  return v;
}

std::vector<std::string> 
cppMCTSeval(DomainDef& domain,
            ProblemDef& problem,
            Scorer scorer,
            TaskGraph& taskgraph,
            std::unordered_map<std::string, std::vector<std::string>>& facts,
            std::vector<int>& times,
            int time_limit = 1000,
            int r = 5,
            double c = 1.4142,
            int seed = 4021,
            std::string const& redis_address = "") {
    domain.set_scorer(scorer);
    pTree t;
    pNode root;
    root.state = KnowledgeBase(domain.predicates,problem.objects,domain.typetree);
    for (auto const& [_,h] : facts) {
      for (auto const& f : h) {
        root.state.tell(f,false,false);
      }
    }
    root.state.update_state();
    root.tasks = taskgraph;
    root.plan = {};
    root.depth = 0;
    int v = t.size();
    t[v] = root;
    static std::mt19937_64 g(seed);
    auto end = seek_evalMCTS(t, v, domain, times, time_limit, r,c,g,redis_address);
    return t[end].plan;
}
