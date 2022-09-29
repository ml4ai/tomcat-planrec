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
                  DomainDef& domain) {
  if (tasks.empty()) {
    json::object obj; 
    obj["tasktree"] = json::value_from(tasktree);
    obj["plan"] = json::value_from(plan);
    double score = domain.score(state)*(1.0/plan.size());
    obj["score"] = score;
    planlib["library"].as_array().emplace_back(obj);
    if (score > planlib["max_score"].as_double()) {
      planlib["max_score"] = score;
    }
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
              for (auto& ai : gts.first) {
                TaskNode t;
                t.task = gts.second[ai].head;
                t.token = gts.second[ai].to_string();
                t.outgoing = gts.second[ai].outgoing;
                gtasktree[ai] = t;
                gtasktree[i].children.push_back(ai);
              }
              seek_planDFS(planlib,plan,gtasktree,state,gts.second,domain);
            }
          }
        }
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
  seek_planDFS(planlib,plan,tasktree,state,tasks,domain);
  return planlib;
}
