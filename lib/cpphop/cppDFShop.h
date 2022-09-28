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
#include <boost/json.hpp>

using json = boost::json;

void seek_planDFS(json::array& planlib, 
                  std::vector<std::string>& plan,
                  TaskTree& tasktree,
                  KnowledgeBase& state,
                  TaskGraph& tasks,
                  DomainDef& domain) {
  if (tasks.empty()) {
    json::object obj; 
    obj.emplace("tasktree",json::value_from(tasktree));
    obj.emplace("plan",json::value_from(plan));
    obj.emplace("score",domain.score(state)*(1.0/plan.size()));
    planlib.emplace_back(obj);
    return;
  }

  for (auto &[i,gt] : tasks.GTs) {
    if (gt.incoming.empty()) {
      if (domain.actions.contains(gt.head)) {
        auto act = domain.actions.at(gt.head).apply(state,gt.args);
        if (!act.second.empty()) {
          auto gtasks = tasks;
          gtasks.remove_node(i);
          for (auto &ns : act.second) {
            ns.update_state();
            auto gplan = plan;
            gplan.push_back(act.first);
            seek_planDFS(planlib,gplan,tasktree,ns,gtasks,domain);
          }
        }
      }
      if (domain.methods.contains(gt.head)) {
        auto task_methods = domain.methods[gt.head];
        for (auto &m : task_methods) {
          auto all_gts = m.apply(state,gt.args,tasks,i);
          if (!all_gts.empty()) {
            for (auto &gts : all_gts) {
              auto gtasktree = tasktree;
              for (auto& ai : g.first) {
                TaskNode t;
                t.task = g.second[ai].head;
                t.token = g.second[ai].to_string();
                t.outgoing = g.second[ai].outgoing;
                gtasktree[ai] = t;
                gtasktree[i].children.push_back(ai);
              }
              seek_planDFS(planlib,plan,gtasktree,state,g.second,domain);
            }
          }
        }
      }
    }
  }
}
