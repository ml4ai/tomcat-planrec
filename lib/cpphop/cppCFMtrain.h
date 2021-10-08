#pragma once

#include "../util.h"
#include "typedefs.h"
#include "Node.h"
#include "Tree.h"
#include "printing.h"
#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include <stack>

template <class State, class Domain, class Selector>
void train_cfmDFS(std::vector<CFM>& cfms, 
                  json& data_team_plan,
                  Tree<State,Selector>& t,
                  int v,
                  Domain& domain) {
  std::stack<int> S;
  S.push(v);
  while (!S.empty()) {
    v = S.top();
    S.pop();
    if (t[v].team_plan["size"] >= data_team_plan["size"] ||
        t[v].tasks.empty()) {
      if (t[v].team_plan == data_team_plan) {
        cfms.push_back(t[v].cfm);
      }
      continue;
    }

    Task task = t[v].tasks.back();
    if (in(task.task_id, domain.operators)) {
      Operator<State> op = domain.operators[task.task_id];
      std::optional<State> newstate = op(t[v].state, task.args);
      if (newstate) {
        pOperator<State> pop = domain.poperators[task.task_id];
        Node<State, Selector> n;
        n.state = newstate.value();
        n.tasks = t[v].tasks;
        n.tasks.pop_back();
        n.depth = t[v].depth + 1;
        n.pred = v;
        n.team_plan = t[v].team_plan;
        json g;
        g["task"] = task2string(task);
        for (auto a : task.agents) {
          n.team_plan["plan"][a].push_back(g);
          n.team_plan["size"] = 1 + n.team_plan["size"].template get<int>();
        }
        int w = boost::add_vertex(n, t);
        t[v].successors.push_back(w);
        S.push(w);
      }
      continue;
    }
    
    if (in(task.task_id, domain.cmethods)) {
      auto relevant = domain.cmethods[task.task_id];
      for (auto cmethod : relevant) {
        cTasks subtasks = cmethod(t[v].state,task.args); 
        if (subtasks.first != "NIL") {
          Node<State, Selector> n;
          n.state = t[v].state;
          n.tasks = t[v].tasks;
          n.tasks.pop_back();
          n.depth = t[v].depth + 1;
          n.team_plan = t[v].team_plan;
          for (auto i = subtasks.second.end();
              i != subtasks.second.begin();) {
            n.tasks.push_back(*(--i));
          }
          n.pred = v;
          n.cfm = t[v].cfm;
          if (n.cfm.find(task.task_id) != n.cfm.end()) {
            if (n.cfm[task.task_id].find(subtasks.first) != n.cfm[task.task_id].end()) {
              n.cfm[task.task_id][subtasks.first] += 1;
            }
            else {
              n.cfm[task.task_id][subtasks.first] = 1;
            }
          }
          else {
            n.cfm[task.task_id][subtasks.first] = 1;
          }
          int w = boost::add_vertex(n,t);
          t[v].successors.push_back(w);
          S.push(w);
        }
      }
      continue;
    }
    std::string message = "Invalid task ";
    message += task.task_id;
    message += " during training!";
    throw std::logic_error(message);
  }
  return;
}

template <class State, class Domain, class Selector>
std::vector<CFM> cppCFMtrain(json& data_team_plan,
                             State state,
                             Tasks tasks, 
                             Selector selector,
                             Domain& domain) {
  std::vector<CFM> cfms = {};
  Tree<State, Selector> t;
  Node<State, Selector> root;
  root.state = state;
  root.tasks = tasks;
  root.depth = 0;
  root.team_plan["size"] = 0;
  root.cfm = {};
  int w = boost::add_vertex(root,t);
  train_cfmDFS(cfms,data_team_plan,t,w,domain);
  return cfms;
}

CFM sumCFMs(std::vector<CFM>& cfms) {
  CFM cfm = cfms.back();
  cfms.pop_back();
  for (const auto& c : cfms) {
    for (const auto& [k1, v1] : c) {
      for (const auto& [k2, v2] : v1) {
        if (cfm.find(k1) != cfm.end()) {
          if (cfm[k1].find(k2) != cfm[k1].end()) {
            cfm[k1][k2] += v2;
          }
          else {
            cfm[k1][k2] = v2;
          }
        }
        else {
          cfm[k1][k2] = v2;
        }
      }
    }   
  }
  return cfm;
}
