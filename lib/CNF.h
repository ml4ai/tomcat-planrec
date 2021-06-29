#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"

namespace ast {
    class DistributeOrOverAnd
        : public boost::static_visitor<std::vector<Clause>> {
      private:
        std::vector<Clause> clauses = {};

      public:
        std::vector<Clause> operator()(Nil s) const { return this->clauses; }
        std::vector<Clause> operator()(AtomicFormula<Term> s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(Literal<Term> s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(AndSentence s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(OrSentence s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(NotSentence s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(ImplySentence s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(ExistsSentence s) const {
            return this->clauses;
        }
        std::vector<Clause> operator()(ForallSentence s) const {
            return this->clauses;
        }
    };

    std::vector<Clause> to_CNF(Sentence s) {
        return boost::apply_visitor(DistributeOrOverAnd(), s);
    }
} // namespace ast
