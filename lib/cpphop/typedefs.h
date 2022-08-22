#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <map>
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
using predicate = std::pair<head,Params>
using Additions = std::vector<predicate>;
using Deletions = std::vector<predicate>;
using Effects = std::pair<Additions,Deletions>;
using condition = std::string;
using CAdditions = std::vector<std::pair<condition,predicate>>;
using CDeletions = std::vector<std::pair<condition,predicate>>;
using CEffects = std::pair<CAdditions,CDeletions>;
using task_token = std::string;
using Task = std::pair<head, Params>;
using Grounded_Task = std::pair<head,Args>;
using Tasks = std::vector<Task>;
using Grounded_Tasks = std::vector<std::pair<head,Args>>;

class Operator {
  Private:
    head name;
    Params parameters;
    Preconds preconditions;
    Effects effects;
    CEffects ceffects;

    std::pair<task_token,KnowledgeBase> apply_binding(KnowledgeBase& kb, Args args) {
      std::string token = "("+this->name;
      for (auto const& [var,t] : this->parameters) {
         token += " "+args.at(var);
      }
      token += ")";
      KnowledgeBase new_kb = kb;
      for (auto const& add : this->effects.first) {
        std::string fact = "("+add.first;
        for (auto const& [var,t] : add.second) {
          fact += " "+args.at(var);
        }
        new_kb.tell(fact+")",false,false);
      }

      for (auto const& del : this->effects.second) {
        std::string fact = "("+del.first;
        for (auto const& [var,t] : del.second) {
          fact += " "+args.at(var);
        }
        new_kb.tell(fact+")",true,false);
      }

      for (auto const& cadd : this->ceffects.first) {
        std::string c;
        if (!args.empty()) {
          c = "(and ";
          for (auto const& [var,val] : args) {
            c += "(= "+var+" "+val+") ";
          }
          c += cadd.first + ")";
        }
        else {
          c = cadd.first;
        }
        auto bindings = kb.ask(c,this->parameters);
        if (!bindings.empty()) {
          std::string fact = "("+cadd.second.first;  
          for (auto const& [var,t] : cadd.second.second) {
            fact += " "+args.at(var); 
          }
          new_kb.tell(fact+")",false,false);
        }
      }

      for (auto const& cdel : this->ceffects.second) {
        std::string c;
        if (!args.empty()) {
          c = "(and ";
          for (auto const& [var,val] : args) {
            c += "(= "+var+" "+val+") ";
          }
          c += cdel.first + ")";
        }
        else {
          c = cdel.first;
        }
        auto bindings = kb.ask(c,this->parameters);
        if (!bindings.empty()) {
          std::string fact = "("+cdel.second.first;  
          for (auto const& [var,t] : cdel.second.second) {
            fact += " "+args.at(var); 
          }
          new_kb.tell(fact+")",true,false);
        }
      }
      new_kb.update_state();
      return std::make_pair(token,new_kb);
    }

  Public:
    Operator(head name, Params parameters, Preconds preconditions, Effects effects, CEffects ceffects) {
      this->name = name;
      this->parameters = parameters;
      this->preconditions = preconditions;
      this->effects = effects;
      this->ceffects = ceffects;
    }

    std::vector<std::pair<task_token,KnowledgeBase>> apply(KnowledgeBase& kb, Args args) {
      std::string pc;
      if (!args.empty()) {
        pc = "(and ";
        for (auto const& [var,val] : args) {
          pc += "(= "+var+" "+val+") ";
        }
        pc += this->preconditions + ")";
      }
      else {
        pc = this->preconditions;
      }
      auto bindings = kb.ask(pc,this->parameters);
      std::vector<std::pair<task_token,KnowledgeBase>> new_states = {};
      for (auto const& b : bindings) {
        new_states.push_back(this->apply_binding(kb,b)) 
      }
      return new_states;
    }
}

class Method {
  Private:
    head name;
    Task task; 
    Params parameters;
    Preconds preconditions;
    Tasks subtasks;

  Public:
    Method(head name, Task task, Params parameters, Preconds preconditions, Tasks subtasks) {
      this->name = name;
      this->task = task;
      this->parameters = parameters;
      this->preconditions = preconditions;
      this->subtasks = subtasks
    }

    std::pair<task_token,Grounded_Tasks> apply_binding(Args args) {
      std::string token = "("+this->task.first;
      for (auto const& [var,t] : this->task.second) {
         token += " "+args.at(var);
      }
      token += ")";
      Grounded_Tasks gts = {};
      for (auto const& s: this->subtasks) {
        Grounded_Task gt;
        gt.first = s.first;
        for (auto const& [var,t] : s.second) {
          gt.second[var] = args.at(var);  
        }
        gts.push_back(gt);
      }
      return std::make_pair(token,gts);
    }

    std::vector<std::pair<task_token,Grounded_Tasks>> apply(KnowledgeBase& kb, Args args) {
      std::string pc;
      if (!args.empty()) {
        pc = "(and ";
        for (auto const& [var,val] : args) {
          pc += "(= "+var+" "+val+") ";
        }
        pc += this->preconditions + ")";
      }
      else {
        pc = this->preconditions;
      }
      auto bindings = kb.ask(pc,this->parameters);
      std::vector<std::pair<task_token,Grounded_Tasks>> groundings;
      for (auto const& b : bindings) {
        groundings.push_back(this->apply_binding(b)) 
      }
      return groundings;
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

using Operators = std::unordered_map<std::string, Operator>;

using Methods = std::unordered_map<std::string, std::vector<Method>>;
