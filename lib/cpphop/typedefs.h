#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
#include <iterator>
#include "kb.h"

using head = std::string;
using var = std::string;
using type = std::string;
using binding = std::string;
using Params = std::unordered_map<var, type>; 
using Args = std::unordered_map<var, binding>;
using Preconds = std::string;
using preds = std::unordered_map<head,Params>;
using Additions = std::unordered_map<head,Params>;
using Deletions = std::unordered_map<head,Params>;
using Effects = std::pair<Additions,Deletions>;
using conds = std::unordered_map<head,Params>;
using CAdditions = std::pair<conds,Additions>;
using CDeletions = std::pair<conds,Deletions>;
using CEffects = std::pair<CAdditions,CDeletions>;
using task_token = std::string;

std::vector<Args> cartProd(Args args1, Args args2) {
  std::vector<Args> new_a = {};
  for (int i = 0; i < args1.size(); i++) {
    for (int j = 0; j < args2.size(); j++) {
      
    }
  }
}

std::vector<Args> get_all_sets(KnowledgeBase& kb,pc, Params params) {
  std::vector<Args> a_set = {}; 
  auto res = ask_vars(kb,pc);
  int perm = 0;
  for (auto const &r : res) {
    perm += res[r.first].size(); 
  }

  for (int i = 0; i < perm; i++) {
    Args a;
    for (auto const &r : res) {

    }
  }
}

struct Operator {
  head name;
  Params parameters;
  Preconds preconditions;
  Effects effects;
  CEffects ceffects;
  Operator(head name, Params parameters, Preconds preconditions, Effects effects, CEffects ceffects) {
    this->name = name;
    this->parameters = parameters;
    this->preconditions = preconditions;
    this->effects = effects;
    this->ceffects = ceffects;
  }

  std::vector<std::pair<task_token,KnowledgeBase>> apply(KnowledgeBase kb, Args args) {
    std::string pc = "(and ";
    for (auto const &p : this->parameters) {
      if (args.find(p.first) != args.end()) {
        pc += "(= "+p.first+" "+args[p.first]+") ";
      }
      pc += "("+p.second+" "+p.first+") ";
    }
    pc += this->preconditions + ")";
    auto res = ask_vars(kb,pc); 

    for (auto const &r : res) {

    }
  }
}
struct DomainDef {
  Operators operators;
  Methods methods;
}

struct ProblemDef {
  KnowledgeBase kb;
  Tasks tasks;
}

struct Task {
  std::string task_id;
  Args args;
  std::vector<std::string> args_order;
  std::vector<std::string> agents;
  Task(std::string t_id, Args a, std::vector<std::string> a_o, std::vector<std::string> as) {
    task_id = t_id;
    args = a;
    args_order = a_o;
    agents = as; 
  }
  //copy constructor
  Task(const Task &t1) {
    task_id = t1.task_id;
    args = t1.args;
    args_order = t1.args_order;
    agents = t1.agents;
  }
};

using Tasks = std::vector<Task>;
using pTasks = std::pair<double, Tasks>;
using cTasks = std::pair<std::string, Tasks>;
using Plans = std::vector<pTasks>;
using cPlans = std::vector<cTasks>;
using Predictions = std::unordered_map<std::string, Task>;

using Operators = std::unordered_map<std::string, Operator>;

template <class State>
using pOperators = std::unordered_map<std::string, pOperator<State>>;

template <class State> using Method = pTasks (*)(State, Args);

template <class State> using cMethod = cTasks (*)(State, Args);

template <class State>
using Methods = std::unordered_map<std::string, std::vector<Method<State>>>;

template <class State>
using cMethods = std::unordered_map<std::string, std::vector<cMethod<State>>>;
