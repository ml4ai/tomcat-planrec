#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"
#include <typeinfo>
#include <iostream>

using boost::get;
using namespace std;

namespace ast {
    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {

        std::vector<Clause> clauses = {};
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const { return s; }
        Sentence operator()(NotSentence s) const { return s; }
        Sentence operator()(ImplySentence s) const { return s; }
        Sentence operator()(ExistsSentence s) const { return s; }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    Sentence to_CNF(Sentence s) {
        auto visitor = DistributeOrOverAnd();
        return boost::apply_visitor(visitor, s);
    }
} // namespace ast
