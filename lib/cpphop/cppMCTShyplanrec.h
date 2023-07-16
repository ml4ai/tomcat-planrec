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
#include "cppMCTShyhop.h"
#include "redis_pipeline.h"
#include "Redis_Connect.h"
#include <boost/json.hpp>
#include <chrono>

namespace json = boost::json;
        
double
simulationhh_rec(std::vector<std::pair<int,std::string>>& actions,
                 std::vector<std::string>& plan,
                 KnowledgeBase state,
                 KnowledgeBase c_state,
                 TaskGraph tasks,
                 DomainDef& domain_htn,
                 DomainDef& domain_c,
                 std::string goal,
                 std::mt19937_64& g) {
  if (!is_subseq(plan,actions)) {
    return -0.5;
  }

  if (plan.size() == actions.size() || state.ask(goal)) {
    return domain_htn.score(state,plan);
  }
  else if (tasks.size() >= actions.size()) {
    std::vector<int> u;
    for (auto &[i,gt] : tasks.GTs) {
      if (gt.incoming.empty()) {
        if (domain_htn.actions.contains(tasks[i].head)) {
          u.push_back(i);
        }
        else if (domain_htn.methods.contains(tasks[i].head)) {
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
      return -0.5;
    }
    auto cTask = *select_randomly(u.begin(),u.end(),g);
    if (domain_htn.actions.contains(tasks[cTask].head)) {
      auto act = domain_htn.actions.at(tasks[cTask].head).apply(state,tasks[cTask].args);
      if (!act.second.empty()) {
        auto gtasks = tasks;
        gtasks.remove_node(cTask);
        auto ns = *select_randomly(act.second.begin(),act.second.end(),g);
        auto gplan = plan;
        gplan.push_back(act.first+"_"+std::to_string(cTask));
        if (gplan.size() < actions.size()) {
          ns.update_state(actions[gplan.size()].first);
        }
        else {
          ns.update_state();
        }
        return simulationhh_rec(actions,
                                gplan,
                                ns,
                                c_state,
                                gtasks,
                                domain_htn,
                                domain_c,
                                goal,
                                g);
      }
      else {
        return -0.5;
      }
    }
    else {
      auto task_methods = domain_htn.methods[tasks[cTask].head];
      auto m = *select_randomly(task_methods.begin(),task_methods.end(),g);
      auto all_gts = m.apply(state,tasks[cTask].args,tasks,cTask);
      if (!all_gts.empty()) {
        auto gts = *select_randomly(all_gts.begin(),all_gts.end(),g);
        return simulationhh_rec(actions,
                                plan,
                                state,
                                c_state,
                                gts.second,
                                domain_htn,
                                domain_c,
                                goal,
                                g);
      }
      else {
        return -0.5;
      }
    }
    return -0.5;
  }
  else {
    std::vector<std::string> actions;
    for (auto &[act,_] : domain_c.actions) {
      actions.push_back(act);
    }
    auto a = *select_randomly(actions.begin(),actions.end(),g);
    auto def = domain_c.actions.at(a);
    auto p = def.apply(c_state);
    if (!p.empty()) {
      auto ns = *select_randomly(p.begin(),p.end(),g);
      ns.second.update_state();
      Grounded_Task gt;
      gt.head = a;
      gt.args = ns.first;
      auto gtasks = tasks;
      gtasks.add_node(gt);
      return simulationhh_rec(actions,
                              plan,
                              state,
                              ns.second,
                              gtasks,
                              domain_htn,
                              domain_c,
                              goal,
                              g);
    }
    else {
      return -1.0;
    }
  }
  return -0.5;
}

int expansionhh_rec(std::vector<std::pair<int,std::string>>& actions,
                    pTree& t,
                    int n,
                    DomainDef& domain_htn,
                    DomainDef& domain_c,
                    std::string goal,
                    std::mt19937_64& g) {
  if (t[n].tasks.size() >= actions.size()) {
    std::vector<int> u;
    for (auto const& [id,gt] : t[n].tasks.GTs) {
      if (gt.incoming.empty()) {
        if (domain_htn.actions.contains(t[n].tasks[id].head)) {
          u.push_back(id);
        }
        else if (domain_htn.methods.contains(t[n].tasks[id].head)) {
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
      return n;
    }
    
    for (auto const& tid : u) {
      if (domain_htn.actions.contains(t[n].tasks[tid].head)) {
        auto act = domain_htn.actions.at(t[n].tasks[tid].head).apply(t[n].state,t[n].tasks[tid].args);
        if (!act.second.empty()) {
          for (auto const& state : act.second) {
            pNode v;
            v.state = state;
            v.c_state = t[n].c_state;
            v.tasks = t[n].tasks;
            v.tasks.remove_node(tid);
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.plan.push_back(act.first+"_"+std::to_string(tid));
            if (v.plan.size() < actions.size()) {
              v.state.update_state(actions[v.plan.size()].first);
              v.time = actions[v.plan.size()].first;
            }
            else {
              v.state.update_state();
            }
            v.treeRoots = t[n].treeRoots;
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].unexplored.push_back(w);
          }
        }
      }
      else {
        for (auto &m : domain_htn.methods[t[n].tasks[tid].head]) {
          auto gts = m.apply(t[n].state,t[n].tasks[tid].args,t[n].tasks,tid);
          for (auto &g : gts) { 
            pNode v;
            v.state = t[n].state;
            v.c_state = t[n].c_state;
            v.tasks = g.second;
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.addedTIDs = g.first;
            v.prevTID = tid;
            v.time = t[n].time;
            v.pred = n;
            v.treeRoots = t[n].treeRoots;
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
    return n;
  }
  else {
    for (auto &[act,def] : domain_c.actions) {
      auto p = def.apply(t[n].c_state);
      for (auto &ns : p) {
        ns.second.update_state();
        Grounded_Task gt;
        gt.head = act;
        gt.args = ns.first;
        pNode v;
        v.c_state = ns.second;
        v.state = t[n].state;
        v.tasks = t[n].tasks;
        int TID = v.tasks.add_node(gt);
        v.depth = t[n].depth + 1;
        v.addedTIDs.push_back(TID);
        v.prevTID = -1; 
        v.treeRoots = t[n].treeRoots;
        v.treeRoots.push_back(TID);
        v.time = t[n].time;
        v.pred = n;
        int w = t.size();
        t[w] = v;
        t[n].unexplored.push_back(w);
      }
    }
    if (!t[n].unexplored.empty()) {
      std::shuffle(t[n].unexplored.begin(),t[n].unexplored.end(),g);
      int r = t[n].unexplored.back();
      t[n].successors.push_back(r);
      t[n].unexplored.pop_back();
      return r;
    }
    return n;
  }
  return n;
}

int
seek_planrecMCTS(pTree& t,
                 TaskTree& tasktree,
                 int v,
                 DomainDef& domain_htn,
                 DomainDef& domain_c,
                 std::string goal,
                 int time_limit,
                 int r,
                 double c,
                 std::mt19937_64& g,
                 std::vector<std::pair<int,std::string>>& actions,
                 std::string const& redis_address) {
  int root = v;
  t[v].time = actions.front().first;
  pTree m;
  pNode n_node;
  if (!redis_address.empty()) {
    t[v].state.update_temporal_facts(redis_address);
  }
  t[v].state.update_state(t[v].time);
  n_node.state = t[v].state;
  n_node.c_state = t[v].c_state;
  n_node.tasks = t[v].tasks;
  n_node.depth = t[v].depth;
  n_node.plan = t[v].plan;
  n_node.time = t[v].time;
  n_node.treeRoots = t[v].treeRoots;
  int w = m.size();
  m[w] = n_node;
  auto start = std::chrono::high_resolution_clock::now();
  auto stop = std::chrono::high_resolution_clock::now();
  while (std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count() < time_limit) {
    int n = selectionhh(m,w,c,g);
    m[n].state.update_state(m[n].time);
    if (w == n && m[n].deadend) {
      std::cout << "Warning: Deadend reached, returning current results!" << std::endl;
      break;
    }
    if (m[n].state.ask(goal) || m[n].plan.size() >= actions.size()) {
        backprophh(m,n,domain_htn.score(m[n].state,m[n].plan),1);
    }
    else {
      if (m[n].sims == 0) {
        m[n].state.update_state(m[n].time);
        double ar = 0.0;
        for (int j = 0; j < r; j++) {
          ar += simulationhh_rec(actions,
                                 m[n].plan,
                                 m[n].state, 
                                 m[n].c_state,
                                 m[n].tasks, 
                                 domain_htn,
                                 domain_c,
                                 goal,
                                 g);
        }
        backprophh(m,n,ar,r);
      }
      else {
        m[n].state.update_state(m[n].time);
        int n_p = expansionhh_rec(actions,
                                  m,
                                  n,
                                  domain_htn,
                                  domain_c,
                                  goal,
                                  g);
        m[n_p].state.update_state(m[n_p].time);
        double ar = 0.0;
        for (int j = 0; j < r; j++) {
          ar += simulationhh_rec(actions,
                                 m[n_p].plan,
                                 m[n_p].state, 
                                 m[n_p].c_state,
                                 m[n_p].tasks, 
                                 domain_htn,
                                 domain_c,
                                 goal,
                                 g);
        }
        backprophh(m,n_p,ar,r);
      }
    }
    stop = std::chrono::high_resolution_clock::now();
  }
  while(!m[w].successors.empty()) {
    std::vector<int> arg_maxes = {};
    double max = -std::numeric_limits<double>::infinity();
    for (auto const &s : m[w].successors) {
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

    if (arg_maxes.empty()) {
      std::cout << "Warning: Deadend reached, returning current results!" << std::endl;
      break;
    }

    w = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.state = m[arg_max].state;
    k.c_state = m[arg_max].c_state;
    k.tasks = m[arg_max].tasks;
    k.plan = m[arg_max].plan;
    k.depth = t[v].depth + 1;
    k.time = m[arg_max].time;
    k.treeRoots = t[v].treeRoots;
    for (auto& i : m[arg_max].addedTIDs) {
      TaskNode tasknode;
      tasknode.task = k.tasks[i].head;
      tasknode.token = k.tasks[i].to_string();
      tasknode.outgoing = k.tasks[i].outgoing;
      tasktree[i] = tasknode;
      if (m[arg_max].prevTID != -1) {
        tasktree[m[arg_max].prevTID].children.push_back(i);
      }
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
  return Results(t,root,v,tasktree);
}

Results 
cppMCTShyplanrec(DomainDef& domain_htn,
                 DomainDef& domain_c,
                 ProblemDef& problem,
                 Scorer scorer,
                 std::vector<std::pair<int,std::string>>& actions,
                 int time_limit = 1000,
                 int r = 5,
                 double c = 1.4142,
                 int seed = 4021,
                 std::string const& redis_address = "") {
    domain_htn.set_scorer(scorer);
    pTree t;
    TaskTree tasktree;
    pNode root;
    root.state = KnowledgeBase(domain_c.predicates,problem.objects,domain_c.typetree);
    for (auto const& f : problem.initF) {
      root.state.tell(f,false,false);
    }
    root.state.update_state();
    root.c_state = root.state;
    root.c_state.update_state();
    root.plan = {};
    root.depth = 0;
    int v = t.size();
    t[v] = root;
    static std::mt19937_64 g(seed);
    return seek_planrecMCTS(t, 
                            tasktree, 
                            v, 
                            domain_htn,
                            domain_c, 
                            problem.goal,
                            time_limit, 
                            r, 
                            c,
                            g,
                            actions,
                            redis_address);
}
