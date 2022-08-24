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

Effects decompose_ceffects(CEffect ceffect) {
  Effects effects = {};
  if (effect.which() == 0) {
    return effects;
  }
  if (effect.which() == 1) {
    auto e = boost::get<AndCEffect>(effect);
    for (auto const& c : e.c_effects) {
      effects.merge(decompose_ceffects(c));
    }
    return effects;
  }
  if (effect.which() == 2) {
    auto e = boost::get<CEffect>(effect);
    effects.merge(decompose_ceffects(c));
    return effects;
  }
  return effects;
}

Effects decompose_effects(Effect effect) {
  Effects effects = {};
  if (effect.which() == 0) {
    return effects;
  }
  if (effect.which() == 1) {
    auto e = boost::get<AndCEffect>(effect);
    for (auto const& c : e.c_effects) {
      effects.merge(decompose_ceffects(c));
    }
    return effects;
  }
  if (effect.which() == 2) {
    auto e = boost::get<CEffect>(effect);
    effects.merge(decompose_ceffects(c));
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

  Actions actions;
  for (auto const& a : dom.actions) {
    std::string name = a.name;
    Params params;
    for (auto const& p : a.parameters.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(p.type);
      for (auto const& e : p.entries) {
        params.push_back(std::make_pair(e.name,type));
      }
    }
    for (auto const& pt : a.parameters.implicitly_typed_list) {
      params.push_back(std::make_pair(pt.name,"__Object__"));
    }
    Preconds preconditions = sentence_to_SMT(a.precondition); 
  }
}
