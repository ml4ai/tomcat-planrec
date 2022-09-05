#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <map>
#include <vector>
#include <iterator>
#include "kb.h"
#include <optional>
#include "util.h"

//{var,type}
using Params = std::vector<std::pair<std::string, std::string>>; 
//{var,val}
using Args = std::vector<std::pair<std::string, std::string>>;
using Preconds = std::string;
using Pred = std::pair<std::string,Params>;
using Predicates = std::vector<Pred>;
struct effect {
  std::string condition;
  bool remove;
  Pred pred;
  std::unordered_map<std::string,std::unordered_set<std::string>> forall;
  effect (std::string condition, bool remove, Pred pred, std::unordered_map<std::string,std::unordered_set<std::string>> forall) {
    this->condition = condition;
    this->remove = remove;
    this->pred = pred;
    this->forall = forall;
  }
};
using Effects = std::vector<effect>;
using task_token = std::string;
using TaskDef = std::pair<std::string, Params>;
using Grounded_Task = std::pair<std::string,Args>;
using TaskDefs = std::vector<TaskDef>;
using Grounded_Tasks = std::vector<Grounded_Task>;
using Objects = std::unordered_map<std::string,std::string>;
using Scorer = double (*)(KnowledgeBase&);
using Scorers = std::unordered_map<std::string, Scorer>;
std::string return_value(std::string var, Args args) {
  for (auto const& a : args) {
    if (var == a.first) {
      return a.second;
    }
  }
  return "__CONST__";
}

Pred create_predicate(std::string head, Params params) {
  Pred pred;
  pred.first = head;
  pred.second = params;
  return pred;
}

class ActionDef {
  private:
    std::string head;
    Params parameters;
    Preconds preconditions;
    Effects effects;

    KnowledgeBase apply_binding(KnowledgeBase& kb, Args args) {
      KnowledgeBase new_kb = kb;
      for (auto const& e : this->effects) {
        auto faparams = e.forall;
        if (faparams.empty()) {
          if (e.condition == "__NONE__") {
            auto pred = e.pred;
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
            new_kb.tell(et+")",e.remove,false);
          }
          else {
            std::string wc;
            if (!args.empty()) {
              wc = "(and ";
              for (int i = 0; i < args.size(); i++) {
                wc += "(= "+this->parameters[i].first+" "+args[i].second+") ";
              }
              wc += e.condition + ")";
            }
            else {
              wc = e.condition;
            }
            auto pass = new_kb.ask(wc,this->parameters);
            if (!pass.empty()) {
              auto pred = e.pred;
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
              new_kb.tell(et+")",e.remove,false);
            }
          }
        }
        else {
          if (e.condition == "__NONE__") {
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
              auto pred = e.pred;
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
              new_kb.tell(et+")",e.remove,false);
            }
          }
          else {
            Params params;
            std::string vt = "(and";
            Params tempP = this->parameters;
            for (auto const& [var,types] : faparams) {
              std::pair<std::string,std::string> arg;
              arg.first = var;
              arg.second = "__Object__";
              params.push_back(arg);
              for (auto const& t : types) {
                vt += " ("+t+" "+var+")";
              }
              for (int i = 0; i < args.size(); i++) {
                if (var == args[i].first) {
                  args.erase(args.begin() + i); 
                }
                if (var == tempP[i].first) {
                  tempP.erase(tempP.begin() + i);
                  tempP.push_back(std::make_pair(var,"__Object__"));
                }
              }
            }
            vt += ")";
            auto bindings = new_kb.ask(vt,params);
            for (auto const& b : bindings) {
              for (auto const& b_args : b) {
                args.push_back(b_args); 
              }
              std::string wc;
              if (!args.empty()) {
                wc = "(and ";
                for (int i = 0; i < args.size(); i++) {
                  wc += "(= "+args[i].first+" "+args[i].second+") ";
                }
                wc += e.condition + ")";
              }
              else {
                wc = e.condition;
              }
              auto pass = new_kb.ask(wc,tempP);
              if (!pass.empty()) {
                auto pred = e.pred;
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
                new_kb.tell(et+")",e.remove,false);
              }
            }
          }
        }
      }
      return new_kb;
    }

  public:
    ActionDef(std::string head, Params parameters, Preconds preconditions, Effects effects) {
      this->head = head;
      this->parameters = parameters;
      this->preconditions = preconditions;
      this->effects = effects;
    }

    std::string get_head() {
      return this->head;
    }

    Params get_parameters() {
      return this->parameters;
    }

    Preconds get_preconditions() {
      return this->preconditions;
    }

    Effects get_effects() {
      return this->effects;
    }

    std::pair<task_token,std::vector<KnowledgeBase>> apply(KnowledgeBase& kb, Args args) {
      std::string pc;
      std::string token = "("+this->head;
      if (!args.empty()) {
        pc = "(and ";
        for (int i = 0; i < args.size(); i++) {
          pc += "(= "+this->parameters[i].first+" "+args[i].second+") ";
          token += " "+args[i].second;
        }
        if (this->preconditions != "__NONE__") {
          pc += this->preconditions + ")";
        }
        else {
          pc += ")";
        }
      }
      else {
        pc = this->preconditions;
      }
      token += ")";

      std::vector<KnowledgeBase> new_states = {};
      if (pc != "__NONE__") {
        if (this->parameters.empty()) {
          auto pass = kb.ask(pc);
          if (pass) {
            new_states.push_back(this->apply_binding(kb,{}));
          }
        }
        else {
          auto bindings = kb.ask(pc,this->parameters);
          for (auto const& b : bindings) {
            new_states.push_back(this->apply_binding(kb,b)); 
          }
        }
      }
      else {
        if (this->parameters.empty()) {
          new_states.push_back(this->apply_binding(kb,{}));
        }
        else {
          auto bindings = kb.ask("",this->parameters);
          for (auto const& b : bindings) {
            new_states.push_back(this->apply_binding(kb,b));
          }
        }
      }
      return std::make_pair(token,new_states);
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
    bool init;

  public:
    MethodDef() {}
    MethodDef(std::string head, TaskDef task, Params parameters, Preconds preconditions, TaskDefs subtasks, bool init = false) {
      this->head = head;
      this->task = task;
      this->parameters = parameters;
      this->preconditions = preconditions;
      //Reverse order for planning algorithm
      this->subtasks = subtasks;
      std::reverse(this->subtasks.begin(),this->subtasks.end());
      this->init = init;
    }

    std::string get_head() {
      return this->head;
    }

    TaskDef get_task() {
      return this->task;
    }

    Params get_parameters() {
      return this->parameters;
    }

    Preconds get_preconditions() {
      return this->preconditions;
    }

    TaskDefs get_subtasks() {
      return this->subtasks;
    }

    Grounded_Tasks apply_binding(Args args) {
      Grounded_Tasks gts = {};
      for (auto const& s: this->subtasks) {
        Grounded_Task gt;
        gt.first = s.first;
        for (auto const& pt : s.second) {
          std::pair<std::string,std::string> arg;
          arg.first = pt.first;
          std::string val = return_value(pt.first,args);
          if (val == "__CONST__") {
            arg.second = pt.first;
          }
          else {
            arg.second = val;
          }
          gt.second.push_back(arg);
        }
        gts.push_back(gt);
      }
      return gts;
    }

    std::pair<task_token,std::vector<Grounded_Tasks>> apply(KnowledgeBase& kb, Args args) {
      std::string pc;
      std::string token = "("+this->task.first;
      if (!args.empty()) {
        pc = "(and ";
        for (int i = 0; i < args.size(); i++) {
          pc += "(= "+this->task.second[i].first+" "+args[i].second+") ";
          token += " "+args[i].second;
        }
        if (this->preconditions != "__NONE__") {
          pc += this->preconditions + ")";
        }
        else {
          pc += ")";
        }
      }
      else {
        pc = this->preconditions;
      }
      token += ")";
      std::vector<Grounded_Tasks> groundings;
      if (pc != "__NONE__") {
        if (this->parameters.empty()) {
          auto pass = kb.ask(pc);
          if (pass) {
            groundings.push_back(this->apply_binding({}));
          }
        }
        else {
          auto bindings = kb.ask(pc,this->parameters);
          for (auto const& b : bindings) {
            groundings.push_back(this->apply_binding(b)); 
          }
        }
      }
      else {
        if (this->parameters.empty()) {
          groundings.push_back(this->apply_binding({}));
        }
        else {
          auto bindings = kb.ask("",this->parameters);
          for (auto const& b : bindings) {
            groundings.push_back(this->apply_binding(b));
          }
        }
      }
      return std::make_pair(token,groundings);
    }
};

using ActionDefs = std::unordered_map<std::string, ActionDef>;
//{Task,vector of the tasks Methods}
using MethodDefs = std::unordered_map<std::string, std::vector<MethodDef>>;

struct DomainDef {
  std::string head;
  TypeTree typetree;
  Predicates predicates;
  TaskDefs tasks;
  ActionDefs actions;
  MethodDefs methods;
  Objects constants;
  Scorer scorer;
  DomainDef(std::string head,
            TypeTree typetree,
            Predicates predicates,
            Objects constants,
            TaskDefs tasks,
            ActionDefs actions,
            MethodDefs methods) {
    this->head = head;
    this->typetree = typetree;
    this->predicates = predicates;
    this->constants = constants;
    this->tasks = tasks;
    this->actions = actions;
    this->methods = methods;
  }
  void set_scorer(Scorer scorer) {
    this->scorer = scorer;
  }

  double score(KnowledgeBase state) {
    return this->scorer(state); 
  }
};

struct ProblemDef {
  std::string head;
  std::string domain_name;
  Objects objects;
  MethodDef initM;
  std::vector<std::string> initF;
  ProblemDef(std::string head,
             std::string domain_name,
             Objects objects,
             MethodDef initM,
             std::vector<std::string> initF) {
    this->head = head;
    this->domain_name = domain_name;
    this->objects = objects;
    this->initM = initM;
    this->initF = initF;
  } 
};
