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

std::string sentence_to_SMT(Sentence sentence) {
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
      cs += " "+sentence_to_SMT(t);
    }
    return cs + ")";
  }
  if (sentence.which() == 3) {
    auto s = boost::get<NotSentence>(sentence);
    std::string ns = "(not";
    ns += " "+sentence_to_SMT(s.sentence);
    return ns + ")";
  }
  if (sentence.which == 4) {
    auto s = boost::get<ImplySentence>(sentence);
    std::string is = "(=>";
    is += " "+sentence_to_SMT(s.sentence1);
    is += " "+sentence_to_SMT(s.sentence2);
  }
  if (sentence.which == 5) {
    auto s = boost::get<QuantifiedSentence>(sentence);
    std::string qs = "("+s.quantifier + "(";
    for (auto const& t : s.variables.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(t.type);
      for (auto const& e : t.entries) {
        qs += "("+e.name+" "+type+") ";
      }
    }
    for (auto const& it : s.variables.implicitly_typed_list) {
      qs += "("+it.name+" __Object__)";
    }
    qs += ")";
    qs += " "+sentence_to_SMT(s.sentence);
    return qs + ")"; 
  }
  return "";
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
  for (auto const& p : dom.predicates) {
    pred pred;
    pred.first = p.predicate;
    Params params;
    for (auto const& t : p.variables.explicitly_typed_lists) {
      std::string type = boost::get<PrimitiveType>(t.type);
      for (auto const& e : t.entries) {
        params[e.name] = type;
      }
    }
    for (auto const& it : p.variables.implicitly_typed_list) {
      params[it.name] = "__Object__";
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
        params[e.name] = type;
      }
    }
    for (auto const& pt : a.parameters.implicitly_typed_list) {
      params[pt.name] = "__Object__";
    }
    Preconds preconditions = sentence_to_SMT(a.precondition); 
  }
}
