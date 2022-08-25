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
//{condition,add=false/remove=true,predicate,extra forall params}
using effect = std::tuple<std::string,bool,pred,std::unordered_map<std::string,std::unordered_set<std::string>>>;
using Effects = std::vector<effect>;
using task_token = std::string;
using TaskDef = std::pair<std::string, Params>;
using Grounded_Task = std::pair<std::string,Args>;
using TaskDefs = std::vector<TaskDef>;
using Grounded_Tasks = std::vector<std::pair<std::string,Args>>;
using Objects = std::unordered_map<std::string,std::string>;

std::string return_value(std::string var, Args args) {
  for (auto const& a : args) {
    if (var == a.first) {
      return a.second;
    }
  }
  return "__CONST__";
}

class ActionDef {
  private:
    std::string head;
    Params parameters;
    Preconds preconditions;
    Effects effects;

    std::pair<task_token,KnowledgeBase> apply_binding(KnowledgeBase& kb, Args args) {
      std::string token = "("+this->head;
      for (auto const& a : args) {
         token += " "+a.second;
      }
      token += ")";
      KnowledgeBase new_kb = kb;
      for (auto const& e : this->effects) {
        if (std::get<0>(e) == "__NONE__") {
          auto faparams = std::get<3>(e);
          if (faparams.empty()) {
            auto pred = std::get<2>(e);
            std::string et = "("+pred.first;
            for (auto const& p : pred.second) {
              auto val = return_value(p.first,args);
              if (val == "__CONST__") {
                et += " "+p.first;
              }
              else {
                et += " "+val;
              }
            }
            new_kb.tell(et+")",std::get<1>(e),false);
          }
          else {
            Params params;
            std::string vt = "(and";
            for (auto const& [var,types] : faparams) {
              std::pair<std::string,std::string> arg;
              arg.first = var;
              arg.second = "__Object__";
              params.push_back(arg);
              for (auto const& t : types) {
                vt += " ("+t+" "+var+")";
              }
            }
            vt += ")";
            auto bindings = new_kb.ask(vt,params);
            for (auto const& b : bindings) {
              auto pred = std::get<2>(e);
              std::string et = "("+pred.first;
              for (auto const& p : pred.second) {
                auto bval = return_value(p.first,b);
                if (bval == "__CONST__") {
                  auto val = return_value(p.first,args); 
                  if (val == "__CONST__") {
                    et += " "+p.first;
                  }
                  else {
                    et += " "+val;
                  }
                }
                else {
                  et += " "+bval;
                }
              }
              new_kb.tell(et+")",std::get<1>(e),false);
            }
          }
        }  
        else if (std::get)
      }
      return std::make_pair(token,new_kb);
    }

  public:
    ActionDef(std::string head, Params parameters, Preconds preconditions, Effects effects) {
      this->head = head;
      this->parameters = parameters;
      this->preconditions = preconditions;
      this->effects = effects;
    }

    std::vector<std::pair<task_token,KnowledgeBase>> apply(KnowledgeBase& kb, Args args) {
      std::string pc;
      if (!args.empty()) {
        pc = "(and ";
        for (int i = 0; i < args.size(); i++) {
          pc += "(= "+this->parameters[i].first+" "+args[i].second+") ";
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
//Ignores task ordering for now! It just assumes that tasks are fully ordered
class MethodDef {
  private:
    std::string head;
    TaskDef task; 
    Params parameters;
    Preconds preconditions;
    TaskDefs subtasks;

  public:
    MethodDef(std::string head, TaskDef task, Params parameters, Preconds preconditions, TaskDefs subtasks) {
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

using ActionDefs = std::unordered_map<std::string, ActionDef>;
//{Task,vector of the tasks Methods}
using MethodDefs = std::unordered_map<std::string, std::vector<MethodDef>>;

struct DomainDef {
  std::string head;
  std::unordered_map<std::string,std::vector<std::string>> types;
  Predicates predicates;
  TaskDefs tasks;
  ActionDefs actions;
  MethodDefs methods;
  Objects constants;
  DomainDef(std::string head,
            std::unordered_map<std::string,std::vector<std::string>> types,
            Predicates predicates,
            Objects constants,
            TaskDefs tasks,
            ActionDefs actions,
            MethodDefs methods) {
    this->head = head;
    this->types = types;
    this->predicates = predicates;
    this->constants = constants;
    this->tasks = tasks;
    this->actions = actions;
    this->methods = methods;
  }
};

