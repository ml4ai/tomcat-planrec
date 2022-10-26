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

namespace json = boost::json;

void seek_planDFS(json::object& planlib, 
                  std::vector<std::string>& plan,
                  TaskTree& tasktree,
                  KnowledgeBase& state,
                  TaskGraph& tasks,
                  int cTask,
                  DomainDef& domain) {
  if (tasks.empty() && cTask == -1) {
    json::object obj; 
    obj["tasktree"] = json::value_from(tasktree);
    obj["plan"] = json::value_from(plan);
    double score = domain.score(state,plan);
    obj["score"] = score;
    bool dup = false;
    for (auto& o : planlib["library"].as_array()) {
      bool match = true;
      for (int i = 0; i < o.as_object()["plan"].as_array().size(); i++) {
        json::string c_act = o.as_object()["plan"].as_array()[i].as_string();
        json::string act = obj["plan"].as_array()[i].as_string();
        if (c_act.subview(0,c_act.find(")") + 1) != act.subview(0,act.find(")") + 1)) {
          match = false; 
          break;
        }
      }
      if (match) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      planlib["library"].as_array().emplace_back(obj);
      if (score > planlib["max_score"].as_double()) {
        planlib["max_score"] = score;
      }
    }
    return;
  }
  if (cTask != -1) {
    if (domain.actions.contains(tasks[cTask].head)) {
      auto act = domain.actions.at(tasks[cTask].head).apply(state,tasks[cTask].args);
      if (!act.second.empty()) {
        auto gtasks = tasks;
        gtasks.remove_node(cTask);
        for (auto &ns : act.second) {
          ns.update_state();
          auto gplan = plan;
          gplan.push_back(act.first+"_"+std::to_string(cTask));
          seek_planDFS(planlib,gplan,tasktree,ns,gtasks,-1,domain);
        }
      }
    }
    if (domain.methods.contains(tasks[cTask].head)) {
      auto task_methods = domain.methods[tasks[cTask].head];
      for (auto &m : task_methods) {
        auto all_gts = m.apply(state,tasks[cTask].args,tasks,cTask);
        if (!all_gts.empty()) {
          for (auto &gts : all_gts) {
            auto gtasktree = tasktree;
            for (auto& ai : gts.first) {
              TaskNode t;
              t.task = gts.second[ai].head;
              t.token = gts.second[ai].to_string();
              t.outgoing = gts.second[ai].outgoing;
              gtasktree[ai] = t;
              gtasktree[cTask].children.push_back(ai);
            }
            seek_planDFS(planlib,plan,gtasktree,state,gts.second,-1,domain);
          }
        }
      }
    }
  }
  else {
    for (auto &[i,gt] : tasks.GTs) {
      if (gt.incoming.empty()) {
        seek_planDFS(planlib,plan,tasktree,state,tasks,i,domain);
      }
    }
  }
}

json::object cppDFShop(DomainDef& domain,
                       ProblemDef& problem,
                       Scorer scorer) {
  domain.set_scorer(scorer);
  json::object planlib;
  json::array library;
  planlib["library"] = library;
  planlib["max_score"] = -std::numeric_limits<double>::infinity();
  std::vector<std::string> plan;
  TaskTree tasktree;
  KnowledgeBase state = KnowledgeBase(domain.predicates,problem.objects,domain.typetree);
  for (auto const& f : problem.initF) {
    state.tell(f,false,false);
  }
  state.update_state();
  TaskGraph tasks;
  Grounded_Task init_t;
  init_t.head = problem.head;
  int TID = tasks.add_node(init_t);
  TaskNode tasknode;
  tasknode.task = init_t.head;
  tasknode.token = init_t.to_string();
  tasktree[TID] = tasknode;
  seek_planDFS(planlib,plan,tasktree,state,tasks,-1,domain);
  json::array actions;
  for (auto const& [a,_] : domain.actions) {
    actions.emplace_back(a);
  }
  planlib["actions"] = actions;
  planlib["root"] = std::to_string(TID);
  return planlib;
}
