#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <queue>
#include <map>
#include <vector>
#include <iterator>
#include "kb.h"
#include <optional>
#include "util.h"
#include <boost/variant/recursive_wrapper.hpp>
#include <boost/json.hpp>

namespace json = boost::json;

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
using TaskDefs = std::unordered_map<std::string,TaskDef>;
using Objects = std::unordered_map<std::string,std::string>;
using Scorer = double (*)(KnowledgeBase&,std::vector<std::string>&);
using Scorers = std::unordered_map<std::string, Scorer>;
using ID = std::string;

struct Grounded_Task {
  std::string head;
  Args args;
  std::vector<int> incoming;
  std::vector<int> outgoing;
  std::string to_string() const {
    std::string s = "("+this->head;
    for (auto const &a : args) {
      s += " "+a.second;
    }
    s += ")";
    return s;
  }
};

struct TaskGraph {
  std::unordered_map<int,Grounded_Task> GTs;
  //Keeps track of next newly usable ID
  int nextID = 0;

  Grounded_Task& operator[](int i) {
    return this->GTs[i];
  }

  int add_node(Grounded_Task& GT) {
    int id;
    id = this->nextID;
    this->nextID++;
    this->GTs[id] = GT;
    return id;
  }

  // gt1 -> gt2
  void add_edge(int gt1, int gt2) {
    this->GTs[gt1].outgoing.push_back(gt2);
    this->GTs[gt2].incoming.push_back(gt1);
  } 

  void remove_node(int gt) {
    for (auto &og : this->GTs[gt].outgoing) {
      this->GTs[og].incoming.erase(std::remove(GTs[og].incoming.begin(),GTs[og].incoming.end(),gt),GTs[og].incoming.end());
    }
    for (auto &ic : this->GTs[gt].incoming) {
      this->GTs[ic].outgoing.erase(std::remove(GTs[ic].outgoing.begin(),GTs[ic].outgoing.end(),gt),GTs[ic].outgoing.end());
    }
    this->GTs.erase(gt);
  }
  
  bool empty() {
    return this->GTs.empty();
  } 

};

struct TaskNode {
  std::string task;
  std::string token;
  std::vector<int> children;
  std::vector<int> outgoing;
};

void tag_invoke(const json::value_from_tag&, json::value& jv, TaskNode const& t) {
  json::array schildren;
  for (auto const& c : t.children) {
    schildren.emplace_back(std::to_string(c));
  } 
  json::array soutgoing;
  for (auto const& o : t.outgoing) {
    soutgoing.emplace_back(std::to_string(o));
  }
  jv = {
      {"task",t.task},
      {"token",t.token},
      {"children",schildren},
      {"outgoing",soutgoing}
  };
}

using TaskTree = std::unordered_map<int,TaskNode>;

void tag_invoke(const json::value_from_tag&, json::value& jv, TaskTree const& t) {
  std::unordered_map<std::string, TaskNode> stasktree;
  for (auto const& [id,n] : t) {
    stasktree[std::to_string(id)] = n;
  }
  jv = json::value_from(stasktree);
}

struct pNode {
    KnowledgeBase state;
    TaskGraph tasks;
    int prevTID = -1;
    std::vector<int> addedTIDs;
    std::vector<std::string> plan;
    int depth = 0;
    double mean = 0.0;
    int sims = 0;
    int pred = -1;
    bool deadend = false;
    std::vector<int> successors = {};
};

using pTree = std::unordered_map<int,pNode>;

struct Results{
  pTree t;
  int root;
  int end;
  TaskTree tasktree;
  int ttRoot;
  Results(pTree t, int root, int end, TaskTree tasktree, int ttRoot) {
    this->t = t;
    this->root = root;
    this->end = end;
    this->tasktree = tasktree;
    this->ttRoot = ttRoot;
  }
};

std::string return_value(std::string var, Args& args) {
  for (auto const& a : args) {
    if (var == a.first) {
      return a.second;
    }
  }
  return "__CONST__";
}

Pred create_predicate(std::string head, Params& params) {
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

    KnowledgeBase apply_binding(KnowledgeBase& kb, Args& args) {
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
            for (auto &b : bindings) {
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
            for (auto &b : bindings) {
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

    std::pair<task_token,std::vector<KnowledgeBase>> apply(KnowledgeBase& kb, Args& args) {
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
            Args b = {};
            new_states.push_back(this->apply_binding(kb,b));
          }
        }
        else {
          auto bindings = kb.ask(pc,this->parameters);
          for (auto &b : bindings) {
            new_states.push_back(this->apply_binding(kb,b)); 
          }
        }
      }
      else {
        if (this->parameters.empty()) {
          Args b = {};
          new_states.push_back(this->apply_binding(kb,b));
        }
        else {
          auto bindings = kb.ask("",this->parameters);
          for (auto &b : bindings) {
            new_states.push_back(this->apply_binding(kb,b));
          }
        }
      }
      return std::make_pair(token,new_states);
    }
};

class MethodDef {
  private:
    std::string head;
    TaskDef task; 
    Params parameters;
    Preconds preconditions;
    TaskDefs subtasks;
    std::unordered_map<std::string,std::vector<std::string>> orderings;

  public:
    MethodDef() {}
    MethodDef(std::string head, 
              TaskDef task, 
              Params parameters, 
              Preconds preconditions, 
              TaskDefs subtasks, 
              std::unordered_map<std::string,std::vector<std::string>> orderings) {
      this->head = head;
      this->task = task;
      this->parameters = parameters;
      this->preconditions = preconditions;
      this->subtasks = subtasks;
      this->orderings = orderings;
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
    
    std::unordered_map<std::string,std::vector<std::string>> get_orderings() {
      return this->orderings;
    }

    std::pair<std::vector<int>,TaskGraph> apply_binding(Args& args, TaskGraph tasks, std::vector<int>& out) {
      std::unordered_map<std::string,int> gts;
      std::vector<int> addedTIDs;
      for (auto const& [id,s]: this->subtasks) {
        Grounded_Task gt;
        gt.head = s.first;
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
          gt.args.push_back(arg);
        }
        gts[id] = tasks.add_node(gt);
        addedTIDs.push_back(gts[id]);
        if (this->orderings[id].empty()) {
          for (auto const& o : out) {
            tasks.add_edge(gts[id],o);
          }
        }
      }
      for (auto const &[t1,ot] : this->orderings) {
        for (auto const &t2 : ot) {
          tasks.add_edge(gts[t1],gts[t2]);
        } 
      }
      return std::make_pair(addedTIDs,tasks);
    }

    std::vector<std::pair<std::vector<int>,TaskGraph>> apply(KnowledgeBase& kb, Args& args, TaskGraph tasks, int i) {
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
      std::vector<std::pair<std::vector<int>,TaskGraph>> groundings;
      std::vector<int> out = tasks[i].outgoing;
      tasks.remove_node(i);
      if (pc != "__NONE__") {
        if (this->parameters.empty()) {
          auto pass = kb.ask(pc);
          if (pass) {
            Args b = {};
            groundings.push_back(this->apply_binding(b,tasks,out));
          }
        }
        else {
          auto bindings = kb.ask(pc,this->parameters);
          for (auto &b : bindings) {
            groundings.push_back(this->apply_binding(b,tasks,out)); 
          }
        }
      }
      else {
        if (this->parameters.empty()) {
          Args b = {};
          groundings.push_back(this->apply_binding(b,tasks,out));
        }
        else {
          auto bindings = kb.ask("",this->parameters);
          for (auto &b : bindings) {
            groundings.push_back(this->apply_binding(b,tasks,out));
          }
        }
      }
      return groundings;
    }
};

using ActionDefs = std::unordered_map<std::string, ActionDef>;
//{Task,vector of the tasks Methods}
using MethodDefs = std::unordered_map<std::string, std::vector<MethodDef>>;

struct DomainDef {
  std::string head;
  TypeTree typetree;
  Predicates predicates;
  ActionDefs actions;
  MethodDefs methods;
  Objects constants;
  Scorer scorer;
  DomainDef(std::string head,
            TypeTree typetree,
            Predicates predicates,
            Objects constants,
            ActionDefs actions,
            MethodDefs methods) {
    this->head = head;
    this->typetree = typetree;
    this->predicates = predicates;
    this->constants = constants;
    this->actions = actions;
    this->methods = methods;
  }
  void set_scorer(Scorer scorer) {
    this->scorer = scorer;
  }

  double score(KnowledgeBase& state, std::vector<std::string>& plan) {
    return this->scorer(state,plan); 
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
