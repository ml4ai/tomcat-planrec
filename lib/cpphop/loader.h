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

struct DomainDef {
  Operators operators;
  Methods methods;
};

struct ProblemDef {
  KnowledgeBase kb;
  Tasks tasks;
};

DomainDef dom_loader(std::string dom_file) {
  std::ifstream f(dom_file);
  std::string s_dom((std::istreambuf_iterator<char>(f)),
                    (std::istreambuf_iterator<char>()));
  return parse<Domain>(s_dom);
}


