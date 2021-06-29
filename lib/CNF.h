#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"

namespace ast {
    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {

        std::vector<Clause> clauses = {};
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(AtomicFormula<Term> s) const { return s; }
        Sentence operator()(Literal<Term> s) const {
            Clause clause;
            clause.literals.push_back(s);
            this->clauses.push_back(clause);
            return s;
        }
        Sentence operator()(AndSentence s) const { return s; }
        Sentence operator()(OrSentence s) const {
            // auto
            return s;
        }
        Sentence operator()(NotSentence s) const { return s; }
        Sentence operator()(ImplySentence s) const { return s; }
        Sentence operator()(ExistsSentence s) const { return s; }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    std::vector<Clause> to_CNF(Sentence s) {
        auto visitor = DistributeOrOverAnd();
        boost::apply_visitor(visitor, s);
        return visitor.clauses;
    }
} // namespace ast
