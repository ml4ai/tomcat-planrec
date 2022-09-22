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

bool is_subseq(std::vector<std::string> v1, std::vector<std::string> v2) {
  if (v1.size() <= v2.size()) {
    for (int i = 0; i < v1.size(); i++) {
      if (v1[i] != v2[i]) {
        return false;
      }
    }
    return true;
  }
  for (int i = 0; i < v2.size(); i++) {
    if (v1[i] != v2[i]) {
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
               DomainDef& domain,
               std::mt19937_64& g,
               int h = 0) {
  if (tasks.empty() || h >= horizon) {
    if (is_subseq(plan,given_plan)) { 
      return domain.score(state);
    }
    return -1.0; 
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
            double rs = csimulation(horizon,ns,gtasks,domain,g,h);
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
        for (auto &m : task_methods) {
          auto all_gts = m.apply(state,gt.args,tasks,i);
          if (!all_gts.second.empty()) {
            std::shuffle(all_gts.second.begin(),all_gts.second.end(),g);
            for (auto &gts : all_gts.second) {
              double rs = csimulation(horizon,state,gts,domain,g,h);
              if (rs > -1.0) {
                return rs;
              }
            }
          }
          else {
            return -1.0;
          }
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

template <class State, class Domain>
int cexpansion_rec(prTree<State>& t,
                  int n,
                  Domain& domain,
                  int seed = 2021) {

    Task task = t.nodes[n].tasks.back();
    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t.nodes[n].state, task.args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task.task_id];
            prNode<State> v;
            v.state = newstate.value();
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.pred = n;
            v.team_plan = t.nodes[n].team_plan;
            json g;
            g["task"] = task2string(task);
            for (auto const &a : task.agents) {
              v.team_plan["plan"][a].push_back(g);
              v.team_plan["size"] = 1 + v.team_plan["size"].template get<int>();
            }
            int w = t.add_node(v);
            t.nodes[n].successors.push_back(w);
            return w;
        }
        std::string message = task.task_id;
        message += " preconditions failed during expansion!";
        throw std::logic_error(
            message);
    }

    if (in(task.task_id, domain.cmethods)) {
        auto relevant = domain.cmethods[task.task_id];
        std::vector<int> c = {};
        for (auto const &cmethod : relevant) {
          cTasks subtasks = cmethod(t.nodes[n].state,task.args);
          if (subtasks.first != "NIL") {
            prNode<State> v;
            v.state = t.nodes[n].state;
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.team_plan = t.nodes[n].team_plan;
            for (auto i = subtasks.second.end();
                i != subtasks.second.begin();) {
              v.tasks.push_back(*(--i));
            }
            v.pred = n;
            int w = t.add_node(v);
            t.nodes[n].successors.push_back(w);
            c.push_back(w);
          }
        }
        //std::cout << total << std::endl;
        seed++;
        if (c.empty()) {   
          std::cout << task.task_id << std::endl;
          return n;
        }
        int r = *select_randomly(c.begin(), c.end(), seed);
        return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain>
int
cseek_planrecMCTS(json& data_team_plan,
                 prTree<State>& t,
                 int v,
                 Domain& domain,
                 int R = 30,
                 double eps = 0.4,
                 int seed = 2021,
                 int aux_R = 10) {

  std::mt19937 gen(seed);
  std::negative_binomial_distribution<int> nbd(50,0.75);
  while (t.nodes[v].team_plan["size"] < data_team_plan["size"]) {
    prTree<State> m;
    prNode<State> n_node;
    n_node.state = t.nodes[v].state;
    n_node.tasks = t.nodes[v].tasks;
    n_node.team_plan = t.nodes[v].team_plan;
    int w = m.add_node(n_node);
    int aux = aux_R;
    int hzn = nbd(gen);
    for (int i = 0; i < R; i++) {
      int n = cselection_rec(m,w,eps,seed);
      seed++;
      if (m.nodes[n].team_plan["size"] >= data_team_plan["size"]) {
          if (m.nodes[n].team_plan["plan"] == data_team_plan["plan"]) {
            cbackprop_rec(m,n,domain.score(m.nodes[n].state));
          }
          else {
            cbackprop_rec(m,n,0.0);
          }
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = csimulation_rec(hzn,
                                   data_team_plan,
                                   m.nodes[n].team_plan,
                                   m.nodes[n].state, 
                                   m.nodes[n].tasks, 
                                   domain, 
                                   seed);
          seed++;
          cbackprop_rec(m,n,r);
        }
        else {
          int n_p = cexpansion_rec(m,n,domain,seed);
          if (n_p == n) {
            if (aux == 0) {
              throw std::logic_error("Out of auxiliary resources, shutting down!");
            }
            aux--;
            i--;
          }
          else {
            aux = aux_R;
          }
          seed++;
          auto r = csimulation_rec(hzn, 
                                   data_team_plan, 
                                   m.nodes[n_p].team_plan, 
                                   m.nodes[n_p].state, 
                                   m.nodes[n_p].tasks, 
                                   domain, 
                                   seed);
          seed++;
          cbackprop_rec(m,n_p,r);   
        }
      }
    }

    int arg_max = m.nodes[w].successors.front();
    double max = m.nodes[arg_max].mean;
    for (int s : m.nodes[w].successors) {
        double mean = m.nodes[s].mean;
        if (mean > max) {
            max = mean;
            arg_max = s;
        }
    }

    prNode<State> k;
    k.state = m.nodes[arg_max].state;
    k.tasks = m.nodes[arg_max].tasks;
    k.team_plan = m.nodes[arg_max].team_plan;
    k.pred = v;
    int y = t.add_node(k);
    t.nodes[v].successors.push_back(y);
    seed++;
    v = y;

    while (m.nodes[arg_max].successors.size() == 1) {
      arg_max = m.nodes[arg_max].successors.front();
      prNode<State> j;
      j.state = m.nodes[arg_max].state;
      j.tasks = m.nodes[arg_max].tasks;
      j.team_plan = m.nodes[arg_max].team_plan;
      j.pred = v;
      int y = t.add_node(j);
      t.nodes[v].successors.push_back(y);
      seed++;
      v = y;
    }
          
  }
  return v;
 
}

template <class State, class Domain>
prResults<State> 
cppMCTSplanrec(json& data_team_plan,
                  State state,
                  Tasks tasks,
                  Domain& domain,
                  int R = 30,
                  double eps = 0.4,
                  int seed = 2021,
                  int aux_R = 10) {
    prTree<State> t;
    prNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.team_plan["size"] = 0;
    int v = t.add_node(root);
    int w = cseek_planrecMCTS(data_team_plan,t, v, domain, R, eps, seed);
    prResults<State> prr;
    prr.t = t;
    prr.root = v;
    prr.end = w;
    return prr;
}
