#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <map>
#include <vector>
#include <iterator>
#include "../kb.h"
#include <optional>

using var = std::string;
using type = std::string;
using binding = std::string;
using Params = std::unordered_map<var, type>; 
using Args = std::unordered_map<var, binding>;
using Preconds = std::string;
using pred = std::pair<std::string,Params>;
using Predicates = std::vector<pred>;
using Additions = std::vector<pred>;
using Deletions = std::vector<pred>;
using Effects = std::pair<Additions,Deletions>;
using condition = std::string;
using CAdditions = std::vector<std::pair<condition,pred>>;
using CDeletions = std::vector<std::pair<condition,pred>>;
using CEffects = std::pair<CAdditions,CDeletions>;
using task_token = std::string;
using Task = std::pair<std::string, Params>;
using Grounded_Task = std::pair<std::string,Args>;
using Tasks = std::vector<Task>;
using Grounded_Tasks = std::vector<std::pair<std::string,Args>>;
using Objects = std::unordered_map<std::string,type>;

class Operator {
  private:
    std::string head;
    Params parameters;
    Preconds preconditions;
    Effects effects;
    CEffects ceffects;

    std::pair<task_token,KnowledgeBase> apply_binding(KnowledgeBase& kb, Args args) {
      std::string token = "("+this->head;
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

  public:
    Operator(std::string head, Params parameters, Preconds preconditions, Effects effects, CEffects ceffects) {
      this->head = head;
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
};

class Method {
  private:
    std::string head;
    Task task; 
    Params parameters;
    Preconds preconditions;
    Tasks subtasks;

  public:
    Method(std::string head, Task task, Params parameters, Preconds preconditions, Tasks subtasks) {
      this->head = head;
      this->task = task;
      this->parameters = parameters;
      this->preconditions = preconditions;
      this->subtasks = subtasks;
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
};

using Operators = std::unordered_map<std::string, Operator>;
using Methods = std::unordered_map<std::string, std::vector<Method>>;

struct DomainDef {
  std::string head;
  std::unordered_map<std::string,std::vector<std::string>> types;
  Predicates predicates;
  Operators operators;
  Methods methods;
  Objects constants;
  DomainDef(std::string head,
            std::unordered_map<std::string,std::vector<std::string>> types,
            Predicates predicates,
            Objects constants,
            Operators operators,
            Methods methods) {
    this->head = head;
    this->types = types;
    this->predicates = predicates;
    this->constants = constants;
    this->operators = operators;
    this->methods = methods;
  }
};

