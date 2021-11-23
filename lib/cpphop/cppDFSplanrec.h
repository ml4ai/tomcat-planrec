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
#include <math.h>
#include <utility>
#include <vector>
#include <stack>
#include <nlohmann/json.hpp>
#include <random>

using json = nlohmann::json;

template <class State>
struct tNode {
    State state;
    Tasks tasks;
    CFM cfm;
    json team_plan;
    double likelihood;
};

template <class State, class Domain>
CFM planrecDFS(json& data_team_plan,
                  tNode<State> v,
                  CPM& cpm,
                  Domain& domain,
                  int seed) {
  CFM max_cfm;
  std::mt19937 gen(seed);
  std::uniform_real_distribution<double> dis(0.0,1.0);
  double max_likelihood = log(0.0); 
  std::stack<tNode<State>> S;
  S.push(v);
  while (!S.empty()) {
    v = S.top();
    S.pop();
    if (v.team_plan["size"] >= data_team_plan["size"] ||
        v.tasks.empty()) {
      if (v.team_plan == data_team_plan) {
        if (v.likelihood >= max_likelihood) {
          max_cfm = v.cfm;
          max_likelihood = v.likelihood;
        }
      }
      continue;
    }

    Task task = v.tasks.back();

    if (in(task.task_id, domain.operators)) {
      Operator<State> op = domain.operators[task.task_id];
      std::optional<State> newstate = op(v.state, task.args);
      if (newstate) {
        pOperator<State> pop = domain.poperators[task.task_id];
        tNode<State> n;
        n.state = newstate.value();
        n.likelihood = v.likelihood + log(pop(v.state,n.state,task.args));
        if (n.likelihood < max_likelihood) {
          continue;
        }
        n.tasks = v.tasks;
        n.tasks.pop_back();
        n.team_plan = v.team_plan;
        json g;
        g["task"] = task2string(task);
        for (auto a : task.agents) {
          n.team_plan["plan"][a].push_back(g);
          n.team_plan["size"] = 1 + n.team_plan["size"].template get<int>();
        }
        n.cfm = v.cfm;
        S.push(n);
      }
      continue;
    }
    
    if (in(task.task_id, domain.cmethods)) {
      auto relevant = domain.cmethods[task.task_id];
      std::vector<cTasks> c = {};
      std::string key = ""; 
      for (auto cmethod : relevant) {
        cTasks subtasks = cmethod(v.state,task.args); 
        if (subtasks.first != "NIL") {
          c.push_back(subtasks);
          if (subtasks.first != "U") {
            key += subtasks.first + "#";
          }
        }
      }
      if (c.empty()) {
        continue;
      }
      for (auto m : c) {
        tNode<State> n;
        if (m.first != "U") {
          if (cpm.find(key) != cpm.end()) {
            if (cpm[key].find(task.task_id) != cpm[key].end()) {
              if (cpm[key][task.task_id].find(m.first) != cpm[key][task.task_id].end()){
                n.likelihood = v.likelihood + log(cpm[key][task.task_id][m.first]);
              }
              else {
                cpm[key][task.task_id][m.first] = dis(gen); 
                n.likelihood = v.likelihood + log(cpm[key][task.task_id][m.first]);
              }
            } 
            else {
              cpm[key][task.task_id][m.first] = dis(gen);
              n.likelihood = v.likelihood + log(cpm[key][task.task_id][m.first]);
            }
          }
          else {
            cpm[key][task.task_id][m.first] = dis(gen);
            n.likelihood = v.likelihood + log(cpm[key][task.task_id][m.first]);
          }
        }
        else {
          n.likelihood = v.likelihood + log(1.0/c.size());
        }
        if (n.likelihood < max_likelihood) {
          continue;
        }
        n.state = v.state;
        n.tasks = v.tasks;
        n.tasks.pop_back();
        n.team_plan = v.team_plan;
        for (auto i = m.second.end();
            i != m.second.begin();) {
          n.tasks.push_back(*(--i));
        }
        n.cfm = v.cfm;
        if (m.first != "U") {
          if (n.cfm.find(key) != n.cfm.end()) {
            if (n.cfm[key].find(task.task_id) != n.cfm[key].end()) {
              if (n.cfm[key][task.task_id].find(m.first) != n.cfm[key][task.task_id].end()) {
                n.cfm[key][task.task_id][m.first] += 1;
              }
              else {
                n.cfm[key][task.task_id][m.first] = 1;
              }
            }
            else {
              n.cfm[key][task.task_id][m.first] = 1;
            }
          }
          else {
            n.cfm[key][task.task_id][m.first] = 1;
          }
        }
        S.push(n);
      }
      continue;
    }
    std::string message = "Invalid task ";
    message += task.task_id;
    message += " during training!";
    throw std::logic_error(message);
  }
  return max_cfm;
}

template <class State, class Domain>
CFM cppDFSplanrec(json& data_team_plan,
                             CPM& cpm,
                             State state,
                             Tasks tasks, 
                             Domain& domain,
                             int seed) {
  tNode<State> root;
  root.state = state;
  root.tasks = tasks;
  root.team_plan["size"] = 0;
  root.cfm = {};
  root.likelihood = 0.0;
  return planrecDFS(data_team_plan,root,cpm,domain,seed);
}

CFM sumCFMs(std::vector<CFM>& cfms) {
  CFM cfm = cfms.back();
  cfms.pop_back();
  for (const auto& c : cfms) {
    for (const auto& [k1, v1] : c) {
      for (const auto& [k2, v2] : v1) {
        for (const auto& [k3,v3] : v2) {
          if (cfm.find(k1) != cfm.end()) {
            if (cfm[k1].find(k2) != cfm[k1].end()) {
              if (cfm[k1][k2].find(k3) != cfm[k1][k2].end()) {
                cfm[k1][k2][k3] += v3;
              }
              else {
                cfm[k1][k2][k3] = v3;
              }
            }
            else {
              cfm[k1][k2][k3] = v3;
            }
          }
          else {
            cfm[k1][k2][k3] = v3;
          }
        }
      }   
    }
  }
  return cfm;
}