#pragma once

#include <fstream>
#include <iostream>
#include <string>

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

namespace x3 = boost::spirit::x3;
using namespace ast;
using boost::get;
using std::string, std::vector, std::unordered_set;
using Ptypes = std::unordered_map<std::string,std::vector<std::string>>;
using Tasktypes = std::unordered_map<std::string,std::vector<std::string>>;

std::unordered_set<std::string> type_inference(Sentence sentence, Ptypes& ptypes, std::string var) {
  std::unordered_set<std::string> types;
  types.insert("__Object__");
  if (sentence.which() == 0) {
    return types; 
  }
  if (sentence.which() == 1) {
    auto s = boost::get<Literal<Term>>(sentence);
    for (int i = 0; i < s.args.size(); i++) {
      if (s.args[i].which() == 1) {
        std::string arg = boost::get<Variable>(s.args[i]).name;
        if (arg == var) {
          types.insert(ptypes[s.predicate][i]);
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
  if (sentence.which == 4) {
    auto s = boost::get<ImplySentence>(sentence);
    types.merge(type_inference(s.sentence1,ptypes,var));
    types.merge(type_inference(s.sentence2,ptypes,var));
    return types;
  }
  if (sentence.which == 5) {
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

std::string sentence_to_SMT(Sentence sentence, PTypes& ptypes) {
  if (sentence.which() == 0) {
    return "()";
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
    for (auto const& t : s.sentences) {
      cs += " "+sentence_to_SMT(t,ptypes);
    }
    return cs + ")";
  }
  if (sentence.which() == 3) {
    auto s = boost::get<NotSentence>(sentence);
    std::string ns = "(not";
    ns += " "+sentence_to_SMT(s.sentence,ptypes);
    return ns + ")";
  }
  if (sentence.which == 4) {
    auto s = boost::get<ImplySentence>(sentence);
    std::string is = "(=>";
    is += " "+sentence_to_SMT(s.sentence1,ptypes);
    is += " "+sentence_to_SMT(s.sentence2,ptypes);
    return is + ")";
  }
  if (sentence.which == 5) {
    auto s = boost::get<QuantifiedSentence>(sentence);
    std::string qs = "("+s.quantifier + " (";
    std::string t_imply = "(=> (and";
    for (auto const& t : s.variables.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(t.type);
      for (auto const& e : t.entries) {
        qs += "("+e.name+" "__Object__") ";
        t_imply += " ("+type+" "+e.name+")"
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
    qs += t_imply+" "+sentence_to_SMT(s.sentence,ptypes);
    return qs + "))"; 
  }
  if (sentence.which == 6) {
    auto s = boost::get<EqualsSentence>(sentence);
    std::string l;
    std::string r;
    if (s.lhs.which == 0) {
      l = boost::get<Constant>(s.lhs).name;
    }
    else {
      l = boost::get<Variable>(s.lhs).name;
    }
    if (s.rhs.which == 0) {
      r = boost::get<Constant>(s.rhs).name;
    }
    else {
      r = boost::get<Variable>(s.rhs).name;
    }

    return "(= "+l+" "+r+")";
  }
  if (sentence.which == 7) {
    auto s = boost::get<NotEqualsSentence>(sentence);
    std::string l;
    std::string r;
    if (s.lhs.which == 0) {
      l = boost::get<Constant>(s.lhs).name;
    }
    else {
      l = boost::get<Variable>(s.lhs).name;
    }
    if (s.rhs.which == 0) {
      r = boost::get<Constant>(s.rhs).name;
    }
    else {
      r = boost::get<Variable>(s.rhs).name;
    }

    return "(not (= "+l+" "+r+"))";
  }
  return "";
}

std::unordered_set<std::string> type_inference(effect e, Ptypes& ptypes, std::string var) {
  std::unordered_set<std::string> types = {"__Object__"};
  auto pred = std::get<2>(e);
  for (int i = 0; i < pred.second.size(); i++) {
    if (var == pred.second[i].first) {
      types.insert(ptypes[pred.first][i]);
    } 
  }
  return types;
}

Effects decompose_ceffects(CEffect ceffect,Ptypes& ptypes) {
  Effects effects = {};
  if (ceffect.which() == 0) {
    auto e = boost::get<ForallCEffect>(ceffect);
    auto faeffects = decompose_effects(e.effect,ptypes);
    for (int i = 0; i < faeffects.size(); i++) {
      for (auto const& v : e.variables) {
        if (std::get<3>(faeffects[i]).find(v.name) == std::get<3>(faeffects[i]).end()) {
          auto types = type_inference(faeffects[i],ptypes,v.name);
          std::get<3>(faeffects[i])[v.name] = types;
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
      pred pd;
      pd.first = p.predicate;
      for (int i = 0; i < p.args.size(); i++) {
        if (p.args[i].which() == 1) {
          std::string arg_name = boost::get<Variable>(p.args[i]).name;
          std::pair<std::string,std::string> arg;
          arg.first = arg_name;
          arg.second = ptypes[p.predicate][i];
          pd.second.push_back(arg);
        } 
        else {
          std::pair<std::string,std::string> arg;
          arg.first = "__CONST__";
          arg.second = ptypes[p.predicate][i];
          pd.second.push_back(arg);
        }
      }
      std::unordered_map<std::string,std::unordered_set<std::string>> fa;
      effects.push_back(std::make_tuple(sentSMT,p.is_negative,pd,fa));
    }
    else {
      auto vp = boost::get<std::vector<PEffect>>(e.cond_effect);
      auto sentSMT = sentence_to_SMT(e.gd, ptypes); 
      for (auto const& p : vp) {
        pred pd;
        pd.first = p.predicate;
        for (int i = 0; i < p.args.size(); i++) {
          if (p.args[i].which() == 1) {
            std::string arg_name = boost::get<Variable>(p.args[i]).name;
            std::pair<std::string,std::string> arg;
            arg.first = arg_name;
            arg.second = ptypes[p.predicate][i];
            pd.second.push_back(arg);
          } 
          else {
            std::pair<std::string,std::string> arg;
            arg.first = "__CONST__";
            arg.second = ptypes[p.predicate][i];
            pd.second.push_back(arg);
          }
        }
        std::unordered_map<std::string,std::unordered_set<std::string>> fa;
        effects.push_back(std::make_tuple(sentSMT,p.is_negative,pd,fa));
      }
    }
    return effects;
  }
  if (ceffect.which() == 2) {
    auto p = boost::get<PEffect>(ceffect);
    pred pd;
    pd.first = p.predicate;
    for (int i = 0; i < p.args.size(); i++) {
      if (p.args[i].which() == 1) {
        std::string arg_name = boost::get<Variable>(p.args[i]).name;
        std::pair<std::string,std::string> arg;
        arg.first = arg_name;
        arg.second = ptypes[p.predicate][i];
        pd.second.push_back(arg);
      } 
      else {
        std::pair<std::string,std::string> arg;
        arg.first = "__CONST__";
        arg.second = ptypes[p.predicate][i];
        pd.second.push_back(arg);
      }
    }
    std::unordered_map<std::string,std::unordered_set<std::string>> fa;
    effects.push_back(std::make_tuple(sentSMT,p.is_negative,pd,fa));
    return effects;
  }
  return effects;
}

Effects decompose_effects(Effect effect, Ptypes& ptypes) {
  Effects effects = {};
  if (effect.which() == 0) {
    return effects;
  }
  if (effect.which() == 1) {
    auto e = boost::get<AndCEffect>(effect);
    for (auto const& c : e.c_effects) {
      effects.merge(decompose_ceffects(c,ptypes));
    }
    return effects;
  }
  if (effect.which() == 2) {
    auto e = boost::get<CEffect>(effect);
    effects.merge(decompose_ceffects(c,ptypes));
    return effects;
  }
  return effects;
}

Domain dom_loader(std::string dom_file) {
  std::ifstream f(dom_file);
  std::string s_dom((std::istreambuf_iterator<char>(f)),
                    (std::istreambuf_iterator<char>()));
  return parse<Domain>(s_dom);
}

DomainDef createDomainDef(Domain dom) {
  std::string name = dom.name; 
  std::unordered_map<std::string,std::vector<std::string>> types;
  for (auto const& t : dom.types.explicitly_typed_lists) {
    std::string type = boost::get<PrimitiveType>(t.type); 
    for (auto const& e : t.entries) {
      types[type].push_back(e);
    }
  }
  for (auto const& it : dom.types.implicitly_typed_list) {
    types["__Object__"].push_back(it.name);
  }

  Predicates predicates;
  Ptypes ptypes;
  for (auto const& p : dom.predicates) {
    pred pred;
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
      constants[e] = type;
    }
  }
  for (auto const& ic : dom.constants.implicitly_typed_list) {
    constants[ic] = "__Object__";
  }

  TaskDefs tasks;
  Tasktypes ttypes;
  for (auto const& t : dom.tasks) {
    TaskDef task;
    task.first = t.name;
    Params params;
    for (auto const& p : t.parameters.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(p.type);
      for (auto const& e : p.entries) {
        params.push_back(std::make_pair(e.name,type));
        ttypes[t.name].push_back(type); 
      }
    }
    for (auto const& pt : t.parameters.implicitly_typed_list) {
      params.push_back(std::make_pair(pt.name,"__Object__"));
      ttypes[t.name].push_back("__Object__");
    }
    task.second = params;
    tasks.push_back(task);
  }

  ActionDefs actions;
  for (auto const& a : dom.actions) {
    TaskDef task;
    std::string name = a.name;
    task.first = a.name;
    Params params;
    Params tparams;
    for (auto const& p : a.parameters.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(p.type);
      for (auto const& e : p.entries) {
        params.push_back(std::make_pair(e.name,type));
        tparams.push_back(std::make_pair(e.name,type));
        ttypes[a.name].push_back(type);
      }
    }
    for (auto const& pt : a.parameters.implicitly_typed_list) {
      params.push_back(std::make_pair(pt.name,"__Object__"));
      tparams.push_back(std::make_pair(pt.name,"__Object__"));
      ttypes[a.name].push_back("__Object__");
    }

    Preconds preconditions = sentence_to_SMT(a.precondition,ptypes); 
    Effects effects = decompose_effects(a.effect,ptypes);
    Action action = Action(name,params,preconditions,effects);
    actions[name] = action; 
    task.second = tparams;
    tasks.push_back(task);
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
      if (m.task.parameters[i].which() == 1) {
        arg.first = boost::get<Variable>(m.task.parameters[i]).name
        arg.second = ttypes[m.task.name][i];
      }
      else {
        arg.first = "__CONST__";
        arg.second = ttypes[m.task.name][i];
      }
      tparams.push_back(arg);
    }
    task.second = tparams;

    Preconds preconditions = sentence_to_SMT(m.precondition,ptypes); 
  }
}
