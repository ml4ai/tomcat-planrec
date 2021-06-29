#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"

namespace ast {
    class DistributeOrOverAnd : public boost::static_visitor<ast::Sentence> {
      public:
        Nil operator()(Nil s) const { return s; }
        AtomicFormula<Term> operator()(AtomicFormula<Term> s) const {
            return s;
        }
        Literal<Term> operator()(Literal<Term> s) const { return s; }
        AndSentence operator()(AndSentence s) const { return s; }
        OrSentence operator()(OrSentence s) const { return s; }
        NotSentence operator()(NotSentence s) const { return s; }
        ImplySentence operator()(ImplySentence s) const { return s; }
        ExistsSentence operator()(ExistsSentence s) const { return s; }
        ForallSentence operator()(ForallSentence s) const { return s; }
    };
} // namespace ast
