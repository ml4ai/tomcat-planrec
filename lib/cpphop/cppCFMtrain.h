#pragma once

#include "../util.h"
#include "typedefs.h"
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
#include <nlohmann/json.hpp>

using json = nlohmann::json;

template <class State>
struct tNode {
    State state;
    Tasks tasks;
    CFM cfm;
    json team_plan;
    int pred = -1;
    std::vector<int> successors = {};
};

template <class State>
using tTree = std::vector<tNode<State>>;

template <class State>
int add_node(tNode<State>& n,tTree<State>& t) {
  t.push_back(n);
  return t.size() - 1;
}

template <class State, class Domain>
void train_cfmDFS(std::vector<CFM>& cfms, 
                  json& data_team_plan,
                  tTree<State>& t,
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
        tNode<State> n;
        n.state = newstate.value();
        n.tasks = t[v].tasks;
        n.tasks.pop_back();
        n.pred = v;
        n.team_plan = t[v].team_plan;
        json g;
        g["task"] = task2string(task);
        for (auto a : task.agents) {
          n.team_plan["plan"][a].push_back(g);
          n.team_plan["size"] = 1 + n.team_plan["size"].template get<int>();
        }
        int w = add_node(n, t);
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
          tNode<State> n;
          n.state = t[v].state;
          n.tasks = t[v].tasks;
          n.tasks.pop_back();
          n.team_plan = t[v].team_plan;
          for (auto i = subtasks.second.end();
              i != subtasks.second.begin();) {
            n.tasks.push_back(*(--i));
          }
          n.pred = v;
          n.cfm = t[v].cfm;
          if (subtasks.first != "U") {
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
          }
          int w = add_node(n,t);
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

template <class State, class Domain>
std::vector<CFM> cppCFMtrain(json& data_team_plan,
                             State state,
                             Tasks tasks, 
                             Domain& domain) {
  std::vector<CFM> cfms = {};
  tTree<State> t;
  tNode<State> root;
  root.state = state;
  root.tasks = tasks;
  root.team_plan["size"] = 0;
  root.cfm = {};
  int w = add_node(root,t);
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
