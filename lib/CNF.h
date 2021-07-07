#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"
#include <iostream>
#include <typeinfo>

using boost::get;
using namespace std;
#include <map>

namespace ast {
    struct GetSentenceType : public boost::static_visitor<std::string> {
        std::string operator()(Nil s) const { return "Nil"; }
        std::string operator()(Literal<Term> s) const { return "Literal"; }
        std::string operator()(ConnectedSentence s) const {
            return "ConnectedSentence";
        }
        std::string operator()(NotSentence s) const { return "NotSentence"; }
        std::string operator()(ImplySentence s) const {
            return "ImplySentence";
        }
        std::string operator()(ExistsSentence s) const {
            return "ExistsSentence";
        }
        std::string operator()(ForallSentence s) const {
            return "ForallSentence";
        }
    };

    struct GeneratePairSentence : public boost::static_visitor<Sentence> {
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
            auto rs = ConnectedSentence();
            rs.connector = (s.connector == "and") ? "and" : "or";
            if (s.sentences.size() <= 2) {
                for (auto sentence : s.sentences) {
                    rs.sentences.push_back(boost::apply_visitor(
                        GeneratePairSentence(), Sentence(sentence)));
                }
                return rs;
            }

            auto last_sen = s.sentences.back();
            s.sentences.pop_back();
            rs.sentences.push_back(
                boost::apply_visitor(GeneratePairSentence(), (Sentence)s));
            rs.sentences.push_back(boost::apply_visitor(GeneratePairSentence(),
                                                        (Sentence)last_sen));
            return rs;
        }
        Sentence operator()(NotSentence s) const { return s; }
        Sentence operator()(ImplySentence s) const { return s; }
        Sentence operator()(ExistsSentence s) const { return s; }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    struct ImplicationsOut : public boost::static_visitor<Sentence> {
        std::vector<Clause> clauses = {};
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
            auto s1 = boost::apply_visitor(ImplicationsOut(),
                                           (Sentence)s.sentences[0]);
            auto s2 = boost::apply_visitor(ImplicationsOut(),
                                           (Sentence)s.sentences[1]);
            ConnectedSentence rs;
            rs.connector = s.connector;
            rs.sentences.push_back(s1);
            rs.sentences.push_back(s2);
            return rs;
        }
        Sentence operator()(NotSentence s) const { return s; }
        Sentence operator()(ImplySentence s) const {
            auto s1 =
                boost::apply_visitor(ImplicationsOut(), (Sentence)s.sentence1);
            auto s2 =
                boost::apply_visitor(ImplicationsOut(), (Sentence)s.sentence2);

            ConnectedSentence rs;
            rs.connector = "or";
            NotSentence rs1;
            rs1.sentence = s1;
            rs.sentences.push_back(rs1);
            rs.sentences.push_back(s2);
            return rs;
        }
        Sentence operator()(ExistsSentence s) const {
            ExistsSentence rs;
            rs.variables = s.variables;
            rs.sentence =
                boost::apply_visitor(ImplicationsOut(), (Sentence)s.sentence);
            return rs;
        }
        Sentence operator()(ForallSentence s) const {
            ForallSentence rs;
            rs.variables = s.variables;
            rs.sentence =
                boost::apply_visitor(ImplicationsOut(), (Sentence)s.sentence);
            return rs;
        }
    };

    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {
        std::vector<Clause> clauses = {};
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
            auto s1 =
                boost::apply_visitor(DistributeOrOverAnd(), s.sentences[0]);
            auto s2 =
                boost::apply_visitor(DistributeOrOverAnd(), s.sentences[1]);

            if (s.connector == "or" and
                boost::apply_visitor(GetSentenceType(), s2) ==
                    "ConnectedSentence") {
                auto s2_ = get<ConnectedSentence>(s2);
                if (s2_.connector == "and") {
                    auto s2_1 = s2_.sentences[0];
                    auto s2_2 = s2_.sentences[1];
                    ConnectedSentence rs1;
                    rs1.connector = "or";
                    rs1.sentences.push_back(s1);
                    rs1.sentences.push_back(s2_1);
                    ConnectedSentence rs2;
                    rs2.connector = "or";
                    rs2.sentences.push_back(s1);
                    rs2.sentences.push_back(s2_2);
                    ConnectedSentence rs;
                    rs.connector = "and";
                    rs.sentences.push_back(boost::apply_visitor(
                        DistributeOrOverAnd(), (Sentence)rs1));
                    rs.sentences.push_back(boost::apply_visitor(
                        DistributeOrOverAnd(), (Sentence)rs2));
                    return rs;
                }
            }

            if (s.connector == "or" and
                boost::apply_visitor(GetSentenceType(), s1) ==
                    "ConnectedSentence") {
                auto s1_ = get<ConnectedSentence>(s1);
                if (s1_.connector == "and") {
                    auto s1_1 = s1_.sentences[0];
                    auto s1_2 = s1_.sentences[1];
                    ConnectedSentence rs1;
                    rs1.connector = "or";
                    rs1.sentences.push_back(s1_1);
                    rs1.sentences.push_back(s2);
                    ConnectedSentence rs2;
                    rs2.connector = "or";
                    rs2.sentences.push_back(s1_2);
                    rs2.sentences.push_back(s2);
                    ConnectedSentence rs;
                    rs.connector = "and";
                    rs.sentences.push_back(boost::apply_visitor(
                        DistributeOrOverAnd(), (Sentence)rs1));
                    rs.sentences.push_back(boost::apply_visitor(
                        DistributeOrOverAnd(), (Sentence)rs2));
                    return rs;
                }
            }

            auto rs = ConnectedSentence();
            rs.connector = s.connector;
            rs.sentences.push_back(s1);
            rs.sentences.push_back(s2);

            return rs;
        }
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
        //        auto s3 =
        //        get<ConnectedSentence>(get<ConnectedSentence>(s2.sentences[1]).sentences[0]);
        //        return boost::apply_visitor(DistributeOrOverAnd(), s1);
    }
} // namespace ast
