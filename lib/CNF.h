#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"
#include <typeinfo>
#include <iostream>
#include <typeinfo>

using boost::get;
using namespace std;

namespace ast {
    struct GeneratePairSentence : public boost::static_visitor<Sentence> {
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
            auto rs = ConnectedSentence();
            rs.connector = (s.connector == "and") ? "and" : "or";
            if (s.sentences.size() <= 2){
                for (auto sentence : s.sentences) {
                    rs.sentences.push_back(boost::apply_visitor(
                        GeneratePairSentence(), Sentence(sentence)));
                }
                return rs;
            }

            auto last_sen = s.sentences.back();
            s.sentences.pop_back();
            rs.sentences.push_back(boost::apply_visitor(GeneratePairSentence(), (Sentence)s));
            rs.sentences.push_back(boost::apply_visitor(GeneratePairSentence(), (Sentence)last_sen));
            return rs;
        }
        Sentence operator()(NotSentence s) const { return s; }
        Sentence operator()(ImplySentence s) const { return s; }
        Sentence operator()(ExistsSentence s) const { return s; }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {

        std::vector<Clause> clauses = {};
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
//            auto a = s.sentences[0];
//            auto b = s.sentences[1].connector;
//            cout << get<ConnectedSentence>(s.sentences[0]).connector;
//            cout << get<ConnectedSentence>(s.sentences[1]).connector;


            return s; }
        Sentence operator()(NotSentence s) const { return s; }
        Sentence operator()(ImplySentence s) const { return s; }
        Sentence operator()(ExistsSentence s) const { return s; }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    Sentence to_CNF(Sentence s) {
//        auto visitor1 = GeneratePairSentence();
        auto s1 = boost::apply_visitor(GeneratePairSentence(), s);
//        auto visitor2 = DistributeOrOverAnd();
//        auto s2 = get<ConnectedSentence>(s1);
//        auto s3 = get<ConnectedSentence>(get<ConnectedSentence>(s2.sentences[1]).sentences[0]);
        return boost::apply_visitor(DistributeOrOverAnd(), s1);
    }
} // namespace ast
