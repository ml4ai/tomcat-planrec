#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"
#include <typeinfo>
#include <iostream>

using boost::get;
using namespace std;

namespace ast {
    std::vector<Clause> to_CNF(Sentence s);
    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {

        std::vector<Clause> clauses = {};
        Sentence operator()(Nil s) const { return s; }
        //        Sentence operator()(AtomicFormula<Term> s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(AndSentence s) const { return s; }
        Sentence operator()(OrSentence s) const {

            auto os = get<OrSentence>(s);
            auto first = os.sentences[0];
            auto second = os.sentences[1];

            std::cout << (typeid(second) == typeid(AndSentence)) << endl;
            std::cout << (typeid(get<AndSentence>(first)) == typeid(AndSentence)) << endl;
            cout << endl;



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
