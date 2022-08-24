#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <map>
#include <vector>
#include <iterator>
#include "../kb.h"
#include <optional>

//{var,type}
using Params = std::vector<std::pair<std::string, std::string>>; 
//{var,val}
using Args = std::vector<std::pair<std::string, std::string>>;
using Preconds = std::string;
using pred = std::pair<std::string,Params>;
using Predicates = std::vector<pred>;
using effect = std::pair<std::string,std::pair<bool,std::string>>;
using Effects = std::vector<effect>;
using task_token = std::string;
using Task = std::pair<std::string, Params>;
using Grounded_Task = std::pair<std::string,Args>;
using Tasks = std::vector<Task>;
using Grounded_Tasks = std::vector<std::pair<std::string,Args>>;
using Objects = std::unordered_map<std::string,std::string>;

class Action {
  private:
    std::string head;
    Params parameters;
    Preconds preconditions;
    Effects effects;
    CEffects ceffects;

    std::pair<task_token,KnowledgeBase> apply_binding(KnowledgeBase& kb, Args args) {
      std::string token = "("+this->head;
      for (auto const& a : args) {
         token += " "+a.second;
      }
      token += ")";
      KnowledgeBase new_kb = kb;
      //fix!
      return std::make_pair(token,new_kb);
    }

  public:
    Action(std::string head, Params parameters, Preconds preconditions, Effects effects, CEffects ceffects) {
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
        for (auto const& vals : args) {
          pc += "(= "+vals.first+" "+vals.second+") ";
        }
        pc += this->preconditions + ")";
      }
      else {
        pc = this->preconditions;
      }
      auto bindings = kb.ask(pc,this->parameters);
      std::vector<std::pair<task_token,KnowledgeBase>> new_states = {};
      for (auto const& b : bindings) {
        new_states.push_back(this->apply_binding(kb,b)); 
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
        groundings.push_back(this->apply_binding(b)); 
      }
      return groundings;
    }
};

using Actions = std::unordered_map<std::string, Action>;
using Methods = std::unordered_map<std::string, std::vector<Method>>;

struct DomainDef {
  std::string head;
  std::unordered_map<std::string,std::vector<std::string>> types;
  Predicates predicates;
  Actions actions;
  Methods methods;
  Objects constants;
  DomainDef(std::string head,
            std::unordered_map<std::string,std::vector<std::string>> types,
            Predicates predicates,
            Objects constants,
            Actions actions,
            Methods methods) {
    this->head = head;
    this->types = types;
    this->predicates = predicates;
    this->constants = constants;
    this->actions = actions;
    this->methods = methods;
  }
};

