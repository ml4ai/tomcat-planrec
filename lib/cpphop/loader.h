#pragma once

#include <fstream>
#include <iostream>
#include <string>
#include <queue>
#include "parsing/api.hpp"
#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/parse.hpp"
#include "util.h"
#include "fol/util.h"
#include <boost/optional.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include "kb.h"
#include "typedefs.h"
#include <filesystem>

namespace fs = std::filesystem;
namespace x3 = boost::spirit::x3;
using namespace ast;
using boost::get;
using std::string, std::vector, std::unordered_set;
using Ptypes = std::unordered_map<std::string,std::vector<std::string>>;
using Tasktypes = std::unordered_map<std::string,std::vector<std::string>>;

void get_orderings(Orderings orderings,std::unordered_map<std::string,std::vector<std::string>>& og) {
  if (which_orderings(orderings) == 0) {
    return;
  }
  if (which_orderings(orderings) == 1) {
    auto o = boost::get<Ordering>(orderings);
    og[o.first].push_back(o.second);
    return;
  }
  if (which_orderings(orderings) == 2) {
    auto ov = boost::get<std::vector<Ordering>>(orderings);
    for (auto const &o : ov) {
      og[o.first].push_back(o.second);
    }
    return;
  }
  return;
};

std::unordered_set<std::string> type_inference(Sentence sentence, Ptypes& ptypes, std::string var) {
  std::unordered_set<std::string> types;
  types.insert("__Object__");
  if (sentence.which() == 0) {
    return types; 
  }
  if (sentence.which() == 1) {
    auto s = boost::get<Literal<Term>>(sentence);
    for (int i = 0; i < s.args.size(); i++) {
      if (s.args.at(i).which() == 1) {
        std::string arg = boost::get<Variable>(s.args.at(i)).name;
        if (arg == var) {
          types.insert(ptypes.at(s.predicate).at(i));
        }
      } 
    }
    return types; 
  }
  if (sentence.which() == 2) {
    auto s = boost::get<ConnectedSentence>(sentence);
    for (auto const& t : s.sentences) {
      types.merge(type_inference(t,ptypes,var));
    }
    return types;
  }
  if (sentence.which() == 3) {
    auto s = boost::get<NotSentence>(sentence);
    types.merge(type_inference(s.sentence,ptypes,var));
    return types;
  }
  if (sentence.which() == 4) {
    auto s = boost::get<ImplySentence>(sentence);
    types.merge(type_inference(s.sentence1,ptypes,var));
    types.merge(type_inference(s.sentence2,ptypes,var));
    return types;
  }
  if (sentence.which() == 5) {
    auto s = boost::get<QuantifiedSentence>(sentence);
    //checks to see if new local scope is created for var
    for (auto const& t : s.variables.explicitly_typed_lists) {
      for (auto const& e : t.entries) {
        if (var == e.name) {
          return types;
        }
      }
    }
    for (auto const& it : s.variables.implicitly_typed_list) {
      if (var == it.name) {
        return types;
      }
    }

    types.merge(type_inference(s.sentence,ptypes,var));
    return types; 
  }
  return types;
}

std::string sentence_to_SMT(Sentence sentence, Ptypes& ptypes) {
  if (sentence.which() == 0) {
    return "__NONE__";
  }
  if (sentence.which() == 1) {
    auto s = boost::get<Literal<Term>>(sentence);
    std::string lt = "("+s.predicate;
    for (auto const& a : s.args) {
      if (a.which() == 0) {
        lt += " "+boost::get<Constant>(a).name;
      }
      else {
        lt += " "+boost::get<Variable>(a).name;
      }
    }
    return lt + ")";
  }
  if (sentence.which() == 2) {
    auto s = boost::get<ConnectedSentence>(sentence);
    std::string cs = "("+s.connector;
    bool all_none = true;
    for (auto const& t : s.sentences) {
      std::string str = sentence_to_SMT(t,ptypes);
      if (str != "__NONE__") {
        cs += " "+str;
        all_none = false;
      }
    }
    if (all_none) {
      return "__NONE__";
    }
    return cs + ")";
  }
  if (sentence.which() == 3) {
    auto s = boost::get<NotSentence>(sentence);
    std::string ns = "(not";
    std::string str = sentence_to_SMT(s.sentence,ptypes);
    if (str != "__NONE__") {
      ns += " "+str;
      return ns + ")";
    }
    return "__NONE__";
  }
  if (sentence.which() == 4) {
    auto s = boost::get<ImplySentence>(sentence);
    std::string is = "(=>";
    std::string str1 = sentence_to_SMT(s.sentence1,ptypes);
    std::string str2 = sentence_to_SMT(s.sentence2,ptypes);
    if (str1 != "__NONE__" && str2 != "__NONE__") {
      is += " "+str1;
      is += " "+str2;
      return is + ")";
    }
    return "__NONE__";
  }
  if (sentence.which() == 5) {
    auto s = boost::get<QuantifiedSentence>(sentence);
    std::string qs = "("+s.quantifier + " (";
    std::string t_imply = "(=> (and";
    if (s.variables.explicitly_typed_lists.empty() && s.variables.implicitly_typed_list.empty()) {
      return "__NONE__";
    }
    for (auto const& t : s.variables.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(t.type);
      for (auto const& e : t.entries) {
        qs += "("+e.name+" __Object__) ";
        t_imply += " ("+type+" "+e.name+")";
      }
    }
    for (auto const& it : s.variables.implicitly_typed_list) {
      qs += "("+it.name+" __Object__) ";
      auto inferred_types = type_inference(s.sentence,ptypes,it.name);
      for (auto const& t : inferred_types) {
        t_imply += " ("+t+" "+it.name+")";
      }
    }
    qs += ") ";
    t_imply += ")";
    std::string str = sentence_to_SMT(s.sentence,ptypes);
    if (str != "__NONE__") {
      qs += t_imply+" "+str;
      return qs + "))";
    }
    return "__NONE__";
  }
  if (sentence.which() == 6) {
    auto s = boost::get<EqualsSentence>(sentence);
    std::string l;
    std::string r;
    if (s.lhs.which() == 0) {
      l = boost::get<Constant>(s.lhs).name;
    }
    else {
      l = boost::get<Variable>(s.lhs).name;
    }
    if (s.rhs.which() == 0) {
      r = boost::get<Constant>(s.rhs).name;
    }
    else {
      r = boost::get<Variable>(s.rhs).name;
    }
    return "(= "+l+" "+r+")";
  }
  if (sentence.which() == 7) {
    auto s = boost::get<NotEqualsSentence>(sentence);
    std::string l;
    std::string r;
    if (s.lhs.which() == 0) {
      l = boost::get<Constant>(s.lhs).name;
    }
    else {
      l = boost::get<Variable>(s.lhs).name;
    }
    if (s.rhs.which() == 0) {
      r = boost::get<Constant>(s.rhs).name;
    }
    else {
      r = boost::get<Variable>(s.rhs).name;
    }
    return "(not (= "+l+" "+r+"))";
  }
  return "__NONE__";
}

std::unordered_set<std::string> type_inference(effect e, Ptypes& ptypes, std::string var) {
  std::unordered_set<std::string> types = {"__Object__"};
  auto pred = e.pred;
  for (int i = 0; i < pred.second.size(); i++) {
    // ORIG: if (var == pred.second.at(i).first) {
    if (var == pred.second.at(i).first) {
      types.insert(ptypes.at(pred.first).at(i));
    } 
  }
  return types;
}
//Forward declaration needed for decompose_effects
Effects decompose_ceffects(CEffect ceffect,Ptypes& ptypes);

Effects decompose_effects(Effect effect, Ptypes& ptypes) {
  Effects effects = {};
  if (effect.which() == 0) {
    return effects;
  }
  if (effect.which() == 1) {
    auto e = boost::get<AndCEffect>(effect);
    for (auto const& c : e.c_effects) {
      effects = merge_vec(effects,decompose_ceffects(c,ptypes));
    }
    return effects;
  }
  if (effect.which() == 2) {
    auto e = boost::get<CEffect>(effect);
    effects = merge_vec(effects,decompose_ceffects(e,ptypes));
    return effects;
  }
  return effects;
}

Effects decompose_ceffects(CEffect ceffect,Ptypes& ptypes) {
  Effects effects = {};
  if (ceffect.which() == 0) {
    auto e = boost::get<ForallCEffect>(ceffect);
    auto faeffects = decompose_effects(e.effect,ptypes);
    for (int i = 0; i < faeffects.size(); i++) {
      for (auto const& v : e.variables) {
        if (faeffects.at(i).forall.find(v.name) == faeffects.at(i).forall.end()) {
          auto types = type_inference(faeffects.at(i),ptypes,v.name);
          faeffects[i].forall[v.name] = types;
        }
      }
    }
    return faeffects;
  }
  if (ceffect.which() == 1) {
    auto e = boost::get<WhenCEffect>(ceffect);
    if (e.cond_effect.which() == 0) {
      auto p = boost::get<PEffect>(e.cond_effect);
      auto sentSMT = sentence_to_SMT(e.gd, ptypes); 
      Pred pd;
      pd.first = p.predicate;
      for (int i = 0; i < p.args.size(); i++) {
        if (p.args.at(i).which() == 1) {
          std::string arg_name = boost::get<Variable>(p.args.at(i)).name;
          std::pair<std::string,std::string> arg;
          arg.first = arg_name;
          arg.second = ptypes.at(p.predicate).at(i);
          pd.second.push_back(arg);
        } 
        else {
          std::pair<std::string,std::string> arg;
          arg.first = boost::get<Constant>(p.args.at(i)).name;
          arg.second = ptypes.at(p.predicate).at(i);
          pd.second.push_back(arg);
        }
      }
      std::unordered_map<std::string,std::unordered_set<std::string>> fa;
      effects.push_back(effect(sentSMT,p.is_negative,pd,fa));
    }
    else {
      auto vp = boost::get<std::vector<PEffect>>(e.cond_effect);
      auto sentSMT = sentence_to_SMT(e.gd, ptypes); 
      for (auto const& p : vp) {
        Pred pd;
        pd.first = p.predicate;
        for (int i = 0; i < p.args.size(); i++) {
          if (p.args.at(i).which() == 1) {
            std::string arg_name = boost::get<Variable>(p.args.at(i)).name;
            std::pair<std::string,std::string> arg;
            arg.first = arg_name;
            arg.second = ptypes.at(p.predicate).at(i);
            pd.second.push_back(arg);
          } 
          else {
            std::pair<std::string,std::string> arg;
            arg.first = boost::get<Constant>(p.args.at(i)).name;
            arg.second = ptypes.at(p.predicate).at(i);
            pd.second.push_back(arg);
          }
        }
        std::unordered_map<std::string,std::unordered_set<std::string>> fa;
        effects.push_back(effect(sentSMT,p.is_negative,pd,fa));
      }
    }
    return effects;
  }
  if (ceffect.which() == 2) {
    auto p = boost::get<PEffect>(ceffect);
    Pred pd;
    pd.first = p.predicate;
    for (int i = 0; i < p.args.size(); i++) {
      if (p.args.at(i).which() == 1) {
        std::string arg_name = boost::get<Variable>(p.args.at(i)).name;
        std::pair<std::string,std::string> arg;
        arg.first = arg_name;
        arg.second = ptypes.at(p.predicate).at(i);
        pd.second.push_back(arg);
      } 
      else {
        std::pair<std::string,std::string> arg;
        arg.first = boost::get<Constant>(p.args.at(i)).name;
        arg.second = ptypes.at(p.predicate).at(i);
        pd.second.push_back(arg);
      }
    }
    std::unordered_map<std::string,std::unordered_set<std::string>> fa;
    effects.push_back(effect("__NONE__",p.is_negative,pd,fa));
    return effects;
  }
  return effects;
}



std::string decompose_constraint(Constraint constraint) {
  if (which_constraint(constraint) == 0) {
    return "__NONE__";
  }
  if (which_constraint(constraint) == 1) {
    auto s = boost::get<EqualsSentence>(constraint);
    std::string l;
    std::string r;
    if (s.lhs.which() == 0) {
      l = boost::get<Constant>(s.lhs).name;
    }
    else {
      l = boost::get<Variable>(s.lhs).name;
    }
    if (s.rhs.which() == 0) {
      r = boost::get<Constant>(s.rhs).name;
    }
    else {
      r = boost::get<Variable>(s.rhs).name;
    }
    return "(= "+l+" "+r+")";
  }
  if (which_constraint(constraint) == 2) {
    auto s = boost::get<NotEqualsSentence>(constraint);
    std::string l;
    std::string r;
    if (s.lhs.which() == 0) {
      l = boost::get<Constant>(s.lhs).name;
    }
    else {
      l = boost::get<Variable>(s.lhs).name;
    }
    if (s.rhs.which() == 0) {
      r = boost::get<Constant>(s.rhs).name;
    }
    else {
      r = boost::get<Variable>(s.rhs).name;
    }
    return "(not (= "+l+" "+r+"))";
  }
  return "__NONE__";
}

std::string decompose_constraints(Constraints constraints) {
  std::string cs = "(and"; 
  if (which_constraints(constraints) == 0) {
    return "__NONE__";
  }
  if (which_constraints(constraints) == 1) {
    auto c = boost::get<Constraint>(constraints);
    std::string str = decompose_constraint(c);
    if (str != "__NONE__") {
      return cs+" "+decompose_constraint(c)+")";
    }
    return "__NONE__";
  }
  if (which_constraints(constraints) == 2) {
    auto cons = boost::get<std::vector<Constraint>>(constraints);
    bool all_none = true;
    for (auto const& c : cons) {
      std::string str = decompose_constraint(c);
      if (str != "__NONE__") {
        cs += " "+decompose_constraint(c); 
        all_none = false;
      }
    }
    if (all_none) {
      return "__NONE__";
    }
    return cs+")"; 
  }
  return "__NONE__";
}

std::vector<std::pair<ID,TaskDef>> get_subtasks(SubTasks subtasks, Tasktypes ttypes) {
  std::vector<std::pair<ID,TaskDef>> subs;
  if (which_subtasks(subtasks) == 0) {
    return subs;
  }
  if (which_subtasks(subtasks) == 1) {
    auto s = boost::get<SubTask>(subtasks);
    if (which_subtask(s) == 0) {
      auto st = boost::get<MTask>(s);
      TaskDef t; 
      t.first = st.name; 
      for (int i = 0; i < st.parameters.size(); i++) {
        if (st.parameters.at(i).which() == 1) {
          std::pair<std::string,std::string> arg;
          arg.first = boost::get<Variable>(st.parameters.at(i)).name; 
          arg.second = ttypes.at(st.name).at(i);
          t.second.push_back(arg);
        } 
        else {
          std::pair<std::string,std::string> arg;
          arg.first = boost::get<Constant>(st.parameters.at(i)).name; 
          arg.second = ttypes.at(st.name).at(i);
          t.second.push_back(arg);
        }
      }
      subs.push_back(std::make_pair("__task0__",t));
    }
    else {
      auto sbtid = boost::get<SubTaskWithId>(s);
      auto st = sbtid.subtask;
      TaskDef t; 
      t.first = st.name; 
      for (int i = 0; i < st.parameters.size(); i++) {
        if (st.parameters.at(i).which() == 1) {
          std::pair<std::string,std::string> arg;
          arg.first = boost::get<Variable>(st.parameters.at(i)).name; 
          arg.second = ttypes.at(st.name).at(i);
          t.second.push_back(arg);
        } 
        else {
          std::pair<std::string,std::string> arg;
          arg.first = boost::get<Constant>(st.parameters.at(i)).name; 
          arg.second = ttypes.at(st.name).at(i);
          t.second.push_back(arg);
        }
      }
      subs.push_back(std::make_pair(sbtid.id,t));
    }
  }
  if (which_subtasks(subtasks) == 2) {
    auto vs = boost::get<std::vector<SubTask>>(subtasks);
    int j = 0;
    for (auto const& s : vs) {
      if (which_subtask(s) == 0) {
        auto st = boost::get<MTask>(s);
        TaskDef t; 
        t.first = st.name; 
        for (int i = 0; i < st.parameters.size(); i++) {
          if (st.parameters.at(i).which() == 1) {
            std::pair<std::string,std::string> arg;
            arg.first = boost::get<Variable>(st.parameters.at(i)).name; 
            arg.second = ttypes.at(st.name).at(i);
            t.second.push_back(arg);
          } 
          else {
            std::pair<std::string,std::string> arg;
            arg.first = boost::get<Constant>(st.parameters.at(i)).name; 
            arg.second = ttypes.at(st.name).at(i);
            t.second.push_back(arg);
          }
        }
        subs.push_back(std::make_pair("__task"+std::to_string(j)+"__",t));
        j++;
      }
      else {
        auto sbtid = boost::get<SubTaskWithId>(s);
        auto st = sbtid.subtask;
        TaskDef t; 
        t.first = st.name; 
        for (int i = 0; i < st.parameters.size(); i++) {
          if (st.parameters.at(i).which() == 1) {
            std::pair<std::string,std::string> arg;
            arg.first = boost::get<Variable>(st.parameters.at(i)).name; 
            arg.second = ttypes.at(st.name).at(i);
            t.second.push_back(arg);
          } 
          else {
            std::pair<std::string,std::string> arg;
            arg.first = boost::get<Constant>(st.parameters.at(i)).name; 
            arg.second = ttypes.at(st.name).at(i);
            t.second.push_back(arg);
          }
        }
        subs.push_back(std::make_pair(sbtid.id,t));
      }
    }
  }
  return subs;
}

Domain dom_loader(std::string dom_file) {
  fs::path filePath = dom_file;
  if (filePath.extension() == ".hddl") {
    std::error_code ec;
    bool exists = fs::exists(filePath,ec);
    if (exists) {
      std::ifstream f(dom_file);
      std::string s_dom((std::istreambuf_iterator<char>(f)),
                        (std::istreambuf_iterator<char>()));
      return parse<Domain>(s_dom);
    }
    throw fs::filesystem_error("No file "+filePath.filename().string()+" found!",ec);
  }
  throw fs::filesystem_error(filePath.extension().string() + " is an invalid extension, only .hddl is a valid extension!",std::error_code());
}

std::pair<DomainDef,Tasktypes> createDomainDef(Domain dom) {
  std::string name = dom.name; 
  TypeTree typetree;
  typetree.add_root("__Object__");
  for (auto const& t : dom.types.explicitly_typed_lists) {
    std::string type = boost::get<PrimitiveType>(t.type); 
    if (typetree.find_type(type) == -1) {
      typetree.add_child(type,"__Object__");  
    }
    for (auto const& e : t.entries) {
      if (typetree.find_type(e) == -1) {
        typetree.add_child(e,type);
      }
      else {
        typetree.add_ancestor(e,type);
      }
    }
  }
  for (auto const& it : dom.types.implicitly_typed_list) {
    if (typetree.find_type(it) == -1) {
      typetree.add_child(it,"__Object__");
    }
  }

  Predicates predicates;
  Ptypes ptypes;
  for (auto const& p : dom.predicates) {
    Pred pred;
    pred.first = p.predicate;
    Params params;
    for (auto const& t : p.variables.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(t.type);
      for (auto const& e : t.entries) {
        params.push_back(std::make_pair(e.name,type));
        ptypes[p.predicate].push_back(type);
      }
    }
    for (auto const& it : p.variables.implicitly_typed_list) {
      params.push_back(std::make_pair(it.name,"__Object__"));
      ptypes[p.predicate].push_back("__Object__");
    }
    pred.second = params;
    predicates.push_back(pred);
  }
  
  Objects constants;
  for (auto const& c : dom.constants.explicitly_typed_lists) {
    std::string type = boost::get<PrimitiveType>(c.type);
    for (auto const& e : c.entries) {
      constants.at(e) = type;
    }
  }
  for (auto const& ic : dom.constants.implicitly_typed_list) {
    constants[ic] = "__Object__";
  }

  Tasktypes ttypes;
  for (auto const& t : dom.tasks) {
    for (auto const& p : t.parameters.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(p.type);
      for (auto const& e : p.entries) {
        ttypes[t.name].push_back(type); 
      }
    }
    for (auto const& pt : t.parameters.implicitly_typed_list) {
      ttypes[t.name].push_back("__Object__");
    }
  }

  ActionDefs actions;
  for (auto const& a : dom.actions) {
    std::string name = a.name;
    Params params;
    for (auto const& p : a.parameters.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(p.type);
      for (auto const& e : p.entries) {
        params.push_back(std::make_pair(e.name,type));
        ttypes[a.name].push_back(type);
      }
    }
    for (auto const& pt : a.parameters.implicitly_typed_list) {
      params.push_back(std::make_pair(pt.name,"__Object__"));
      ttypes[a.name].push_back("__Object__");
    }

    Preconds preconditions = sentence_to_SMT(a.precondition,ptypes); 
    Effects effects = decompose_effects(a.effect,ptypes);
    actions.emplace(std::make_pair(name, ActionDef(name,params,preconditions,effects))); 
  }
  
  MethodDefs methods;
  for (auto const& m : dom.methods) {
    TaskDef task;
    std::string name = m.name;
    task.first = m.task.name;
    Params params;
    Params tparams;
    for (auto const& p : m.parameters.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(p.type);
      for (auto const& e : p.entries) {
        params.push_back(std::make_pair(e.name,type));
      }
    }
    for (auto const& pt : m.parameters.implicitly_typed_list) {
      params.push_back(std::make_pair(pt.name,"__Object__"));
    }

    for (int i = 0; i < m.task.parameters.size(); i++) {
      std::pair<std::string,std::string> arg;
      if (m.task.parameters.at(i).which() == 1) {
        arg.first = boost::get<Variable>(m.task.parameters.at(i)).name;
        arg.second = ttypes.at(m.task.name).at(i);
      }
      else {
        arg.first =  boost::get<Constant>(m.task.parameters.at(i)).name;
        arg.second = ttypes.at(m.task.name).at(i);
      }
      tparams.push_back(arg);
    }
    task.second = tparams;

    Preconds preconditions = sentence_to_SMT(m.precondition,ptypes); 

    if (m.task_network.constraints) {
      std::string cs = decompose_constraints(*m.task_network.constraints);
      if (cs != "__NONE__") {
        preconditions = "(and "+preconditions+" "+cs+")";
      }
    }
     
    TaskDefs subtasks;
    std::unordered_map<std::string,std::vector<std::string>> orderings;
    if (m.task_network.subtasks) {
      auto sts = get_subtasks(m.task_network.subtasks->subtasks,ttypes);    
      if (m.task_network.subtasks->ordering_kw == "ordered-tasks" || 
          m.task_network.subtasks->ordering_kw == "ordered-subtasks") {
        subtasks[sts[0].first] = sts.at(0).second;
        for (int i = 1; i < sts.size(); i++) {
          subtasks[sts[i].first] = sts.at(i).second;
          orderings[sts[i-1].first].push_back(sts.at(i).first);
        }
        orderings[sts[sts.size()-1].first] = {};
      }
      else {
        if (!m.task_network.orderings) {
          for (auto const &st : sts) {
            subtasks[st.first] = st.second;
            orderings[st.first] = {};
          }
        } 
        else {
          for (auto const &st : sts) {
            subtasks[st.first] = st.second;
            orderings[st.first] = {};
          }
          get_orderings(*m.task_network.orderings,orderings); 
        }
      }
    }

    methods[m.task.name].push_back(MethodDef(name,task,params,preconditions,subtasks,orderings));
  }
  auto DD = DomainDef(name,typetree,predicates,constants,actions,methods);
  return std::make_pair(DD,ttypes);
}

std::pair<DomainDef,Tasktypes> loadDomain(std::string dom_file) {
  Domain dom = dom_loader(dom_file);
  return createDomainDef(dom);
}

Problem prob_loader(std::string prob_file) {
  fs::path filePath = prob_file;
  if (filePath.extension() == ".hddl") {
    std::error_code ec;
    bool exists = fs::exists(filePath,ec);
    if (exists) {
      std::ifstream f(prob_file);
      std::string s_prob((std::istreambuf_iterator<char>(f)),
                        (std::istreambuf_iterator<char>()));
      return parse<Problem>(s_prob);
    }
    throw fs::filesystem_error("No file "+filePath.filename().string()+" found!",ec);
  }
  throw fs::filesystem_error(filePath.extension().string() + " is an invalid extension, only .hddl is a valid extension!",std::error_code());
}

ProblemDef createProblemDef(Problem prob, Tasktypes ttypes) {
  std::string head = "__"+prob.name+"__";
  std::string domain_name = prob.domain_name;

  Objects objects;
  for (auto const& o : prob.objects.explicitly_typed_lists) {
    std::string type = boost::get<PrimitiveType>(o.type);
    for (auto const& e : o.entries) {
      objects[e] = type;
    }
  }
  for (auto const& io : prob.objects.implicitly_typed_list) {
    objects[io] = "__Object__";
  }
  
  std::string m_name = prob.problem_htn.problem_class;
  TaskDef task;
  task.first = head;
  task.second = {};
  Params params;
  for (auto const& p : prob.problem_htn.parameters.explicitly_typed_lists) {
    std::string type = boost::get<PrimitiveType>(p.type);
    for (auto const& e : p.entries) {
      params.push_back(std::make_pair(e.name,type));
    }
  }
  for (auto const& pt : prob.problem_htn.parameters.implicitly_typed_list) {
    params.push_back(std::make_pair(pt.name,"__Object__"));
  }
  Preconds preconditions;
  if (prob.problem_htn.task_network.constraints) {
    std::string cs = decompose_constraints(*prob.problem_htn.task_network.constraints);
    preconditions = cs;
  }
  else {
    preconditions = "__NONE__";
  }

  TaskDefs subtasks;
  std::unordered_map<std::string,std::vector<std::string>> orderings;
  if (prob.problem_htn.task_network.subtasks) {
    auto sts = get_subtasks(prob.problem_htn.task_network.subtasks->subtasks,ttypes);    
    if (prob.problem_htn.task_network.subtasks->ordering_kw == "ordered-tasks" || 
        prob.problem_htn.task_network.subtasks->ordering_kw == "ordered-subtasks") {
      subtasks[sts[0].first] = sts.at(0).second;
      for (int i = 1; i < sts.size(); i++) {
        //subtasks.at(sts.at(i).first) = sts.at(i).second;
        //safe below.
        subtasks[sts[i].first] = sts.at(i).second;
        orderings[sts[i-1].first].push_back(sts.at(i).first);
      }
      orderings[sts[sts.size()-1].first] = {};
    }
    else {
      if (!prob.problem_htn.task_network.orderings) {
        for (auto const &st : sts) {
          subtasks[st.first] = st.second;
          orderings[st.first] = {};
        }
      } 
      else {
        for (auto const &st : sts) {
          subtasks[st.first] = st.second;
          orderings[st.first] = {};
        }
        get_orderings(*prob.problem_htn.task_network.orderings, orderings); 
      }
    }
  }

  MethodDef initM = MethodDef(m_name,task,params,preconditions,subtasks,orderings);

  std::vector<std::string> initF;
  for (auto const& i : prob.init) {
    std::string pred = "("+i.predicate;
    for (auto const& a : i.args) {
      pred += " "+a;
    }
    pred += ")";
    initF.push_back(pred);
  }
  return ProblemDef(head,domain_name,objects,initM,initF);
}

ProblemDef loadProblem(std::string prob_file, Tasktypes ttypes) {
  Problem prob = prob_loader(prob_file);
  return createProblemDef(prob,ttypes);
}

std::pair<DomainDef, ProblemDef> load(std::string dom_file, std::string prob_file) {
  auto dom = loadDomain(dom_file);
  auto probDef = loadProblem(prob_file,dom.second);
  if (dom.first.head == probDef.domain_name) {
    dom.first.methods[probDef.initM.get_task().first].push_back(probDef.initM);
    probDef.objects.merge(dom.first.constants);
    return std::make_pair(dom.first,probDef);
  }
  throw std::invalid_argument("Loaded Domain Definition is for "+
                              dom.first.head+
                              ", but was given a Problem Definition "+
                              probDef.head+
                              " for Domain Definition "+
                              probDef.domain_name+"!");
}
