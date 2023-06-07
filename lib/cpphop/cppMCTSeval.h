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
                int cTask,
                std::vector<int>& times,
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
          auto gplan = plan;
          gplan.push_back(act.first+"_"+std::to_string(cTask));
          if (gplan.size() == times.size()) {
            ns.update_state();
            return domain.score(ns,gplan);
          }
          ns.update_state(times[gplan.size()]);
          double rs = simulation_eval(gplan,ns,gtasks,-1,times,domain,g);
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
            double rs = simulation_eval(plan,state,gts.second,-1,times,domain,g);
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
        double rs = simulation_eval(plan,state,tasks,i,times,domain,g);
        if (rs > -1.0) {
          return rs;
        }
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
    if (t[n].cTask != -1) {
      int tid = t[n].cTask;
      if (domain.actions.contains(t[n].tasks[tid].head)) {
        auto act = domain.actions.at(t[n].tasks[tid].head).apply(t[n].state,t[n].tasks[tid].args);
        if (!act.second.empty()) {
          std::vector<int> a;
          for (auto const& state : act.second) {
            pNode v;
            v.state = state;
            v.tasks = t[n].tasks;
            v.tasks.remove_node(tid);
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.time = t[n].time + 1;
            v.plan.push_back(act.first+"_"+std::to_string(tid));
            if (times.size() == v.plan.size()) {
              v.state.update_state();
            }
            else {
              v.state.update_state(times[v.plan.size()]);
            }
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
          v.time = t[n].time;
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
seek_evalMCTS(pTree& t,
              int v,
              DomainDef& domain,
              std::vector<int>& times,
              int R,
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
    for (int i = 0; i < R; i++) {
      int n = selection(m,w,c,g);
      if (m[n].tasks.empty() && m[n].cTask == -1) {
          backprop(m,n,domain.score(m[n].state,m[n].plan),1);
      }
      else {
        if (m[n].sims == 0) {
          m[n].state.update_state(m[n].time);
          double ar;
          for (int j = 0; j < r; j++) {
            ar += simulation_eval(m[n].plan,
                                  m[n].state, 
                                  m[n].tasks, 
                                  m[n].cTask,
                                  times,
                                  domain,
                                  g);
          }
          if (ar <= -r) {
            m[n].deadend = true;
          }
          backprop(m,n,ar,r);
        }
        else {
          m[n].state.update_state(m[n].time);
          int n_p = expansion_eval(m,n,domain,times,g);
          m[n_p].state.update_state(m[n_p].time);
          double ar;
          for (int j = 0; j < r; j++) {
            ar += simulation_eval(m[n_p].plan,
                                  m[n_p].state, 
                                  m[n_p].tasks, 
                                  m[n_p].cTask,
                                  times,
                                  domain,
                                  g);
          }
          if (ar <= -r) {
            m[n_p].deadend = true;
          }
          backprop(m,n_p,ar,r);
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
    k.pred = v;
    int y = t.size();
    t[y] = k;
    t[v].successors.push_back(y);
    v = y;
    if (t[v].plan.size() >= times.size()) {
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
      j.pred = v;
      int y = t.size();
      t[y] = j;
      t[v].successors.push_back(y);
      v = y;

      if (t[v].plan.size() >= times.size()) {
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

std::vector<std::string> 
cppMCTSeval(DomainDef& domain,
            ProblemDef& problem,
            Scorer scorer,
            TaskGraph& taskgraph,
            std::unordered_map<std::string, std::vector<std::string>>& facts,
            std::vector<int>& times,
            int R = 30,
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
    auto end = seek_evalMCTS(t, v, domain, times, R, r,c,g,redis_address);
    return t[end].plan;
}
