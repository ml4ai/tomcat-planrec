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

template <class State, class Domain>
void train_cfmDFS(std::vector<CFM>& cfms, 
                  CFM cfm,
                  json& data_team_plan,
                  json team_plan,
                  Tasks tasks, 
                  State state, 
                  Domain& domain) {
  if (team_plan["size"] >= data_team_plan["size"]) {
    if (team_plan["plan"] == data_team_plan["plan"]) {
      cfms.push_back(cfm);
    }
    return;
  }

  Task task = tasks.back();

  if (in(task.task_id, domain.operators)) {
    Operator<State> op = domain.operators[task.task_id];
    std::optional<State> newstate = op(state,task.args);
    if (newstate) {
      pOperator<State> pop = domain.poperators[task.task_id];
      tasks.pop_back();
      json g;
      g["task"] = task2string(task);
      state = newstate.value();
      for (auto a : task.agents) {
        team_plan["plan"][a].push_back(g);
        team_plan["size"] = 1 + team_plan["size"].get<int>();
      }
      train_cfmDFS(cfms,cfm,data_team_plan,team_plan,tasks,state,domain);
    }
    return;
  }

  if (in(task.task_id, domain.cmethods)) {
    auto relevant = domain.cmethods[task.task_id];
    for (auto cmethod : relevant) {
      cTasks subtasks = cmethod(state, task.args);
      if (subtasks.first != "NIL") {
        if (cfm.find(task.task_id) != cfm.end()) {
          if(cfm[task.task_id].find(subtasks.first) != cfm[task.task_id].end()) {
            cfm[task.task_id][subtasks.first] += 1;
          }
          else {
            cfm[task.task_id][subtasks.first] = 1;
          }
        }
        else {
          cfm[task.task_id][subtasks.first] = 1;
        }
      }
      Tasks new_tasks = tasks;
      new_tasks.pop_back();
      for (auto i = subtasks.second.end();
          i != subtasks.second.begin();) {
        new_tasks.push_back(*(--i));
      }
      train_cfmDFS(cfms,cfm,data_team_plan,team_plan,new_tasks,state,domain);
    }
    return;
  }   
  std::string message = "Invalid task ";
  message += task.task_id;
  message += " during training!";
  throw std::logic_error(message);
}

template <class State, class Domain>
std::vector<CFM> cppCFMtrain(json& data_team_plan,
                             Tasks tasks, 
                             State state,
                             Domain& domain, 
                             std::vector<CFM> cfms = {}) {
  CFM cfm = {};
  json team_plan;
  team_plan["size"] = 0;
  train_cfmDFS(cfms,cfm,data_team_plan,team_plan,tasks,state,domain);
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
