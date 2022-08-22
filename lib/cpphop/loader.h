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
    pred.second = params;
    predicates.push_back(pred);
  }
}
