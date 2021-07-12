#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "parsing/ast.hpp"
#include <iostream>
#include <typeinfo>
#include <map>

using boost::get;
using namespace std;

namespace ast {
    bool contains(auto v, auto x) {
        if(std::find(v.begin(), v.end(), x) != v.end()) {
            return true;
        } else {
            return false;
        }
      }

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

    struct NegationsIn : public boost::static_visitor<Sentence> {
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
            auto s1 =
                boost::apply_visitor(NegationsIn(), (Sentence)s.sentences[0]);
            auto s2 =
                boost::apply_visitor(NegationsIn(), (Sentence)s.sentences[1]);
            ConnectedSentence rs;
            rs.connector = s.connector;
            rs.sentences.push_back(s1);
            rs.sentences.push_back(s2);
            return rs;
        }
        Sentence operator()(NotSentence s) const {
            auto s1 = s.sentence;
            if (boost::apply_visitor(GetSentenceType(), (Sentence)s1) ==
                "NotSentence") {
                auto s_ = get<NotSentence>(s1);
                return boost::apply_visitor(NegationsIn(),
                                            (Sentence)s_.sentence);
            }

            if (boost::apply_visitor(GetSentenceType(), (Sentence)s1) ==
                "ConnectedSentence") {
                auto s_ = get<ConnectedSentence>(s1);
                auto s_1 = s_.sentences[0];
                auto s_2 = s_.sentences[1];
                if (s_.connector == "and") {
                    ConnectedSentence rs;
                    NotSentence rs1;
                    rs1.sentence = s_1;
                    NotSentence rs2;
                    rs2.sentence = s_2;
                    rs.connector = "or";
                    rs.sentences.push_back(
                        boost::apply_visitor(NegationsIn(), (Sentence)rs1));
                    rs.sentences.push_back(
                        boost::apply_visitor(NegationsIn(), (Sentence)rs2));
                    return rs;
                }
                if (s_.connector == "or") {
                    ConnectedSentence rs;
                    NotSentence rs1;
                    rs1.sentence = s_1;
                    NotSentence rs2;
                    rs2.sentence = s_2;
                    rs.connector = "and";
                    rs.sentences.push_back(
                        boost::apply_visitor(NegationsIn(), (Sentence)rs1));
                    rs.sentences.push_back(
                        boost::apply_visitor(NegationsIn(), (Sentence)rs2));
                    return rs;
                }
            }

            if (boost::apply_visitor(GetSentenceType(), (Sentence)s1) ==
                "ForallSentence") {
                auto s_ = get<ForallSentence>(s1);
                NotSentence rs1;
                rs1.sentence = s_.sentence;
                auto rs2 = boost::apply_visitor(NegationsIn(), (Sentence)rs1);
                ExistsSentence rs;
                rs.variables = s_.variables;
                rs.sentence = rs2;
                return rs;
            }

            if (boost::apply_visitor(GetSentenceType(), (Sentence)s1) ==
                "ExistsSentence") {
                auto s_ = get<ExistsSentence>(s1);
                NotSentence rs1;
                rs1.sentence = s_.sentence;
                auto rs2 = boost::apply_visitor(NegationsIn(), (Sentence)rs1);
                ForallSentence rs;
                rs.variables = s_.variables;
                rs.sentence = rs2;
                return rs;
            }

            NotSentence rs;
            rs.sentence = boost::apply_visitor(NegationsIn(), (Sentence)s1);

            return rs;
        }
        Sentence operator()(ImplySentence s) const {
            auto s1 =
                boost::apply_visitor(NegationsIn(), (Sentence)s.sentence1);
            auto s2 =
                boost::apply_visitor(NegationsIn(), (Sentence)s.sentence2);

            ImplySentence rs;
            rs.sentence1 = s1;
            rs.sentence2 = s2;
            return rs;
        }
        Sentence operator()(ExistsSentence s) const {
            ExistsSentence rs;
            rs.variables = s.variables;
            rs.sentence =
                boost::apply_visitor(NegationsIn(), (Sentence)s.sentence);
            return rs;
        }
        Sentence operator()(ForallSentence s) const {
            ForallSentence rs;
            rs.variables = s.variables;
            rs.sentence =
                boost::apply_visitor(NegationsIn(), (Sentence)s.sentence);
            return rs;
        }
    };

    struct StandardizeApartIndexical {
        int index = 0;
        std::string getPrefix() {
            return "q";
        }
        int getNextIndex() {
            return this->index++;
        }
    };

    struct StandardizeQuantiferVariables
        : public boost::static_visitor<Sentence> {
        ast::StandardizeApartIndexical quantifiedIndexical;
        int i = quantifiedIndexical.getNextIndex();

        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const {
            auto s1 =
                boost::apply_visitor(StandardizeQuantiferVariables(), (Sentence)s.sentences[0]);
            auto s2 =
                boost::apply_visitor(StandardizeQuantiferVariables(), (Sentence)s.sentences[1]);
            ConnectedSentence rs;
            rs.connector = s.connector;
            rs.sentences.push_back(s1);
            rs.sentences.push_back(s2);
            return rs;
        }
        Sentence operator()(NotSentence s) const {
            NotSentence rs;
            rs.sentence = boost::apply_visitor(StandardizeQuantiferVariables(), (Sentence)s.sentence);
            return rs;
        }

        Sentence operator()(ImplySentence s) const { return s; }
        // can't be constant
        Sentence operator()(ExistsSentence s, vector<Variable> arg) {
            vector<Variable> seenSoFar = arg;
            std::map<Variable, Term> localSubst;
            std::vector<Variable> replVariables;
            for (auto & v : s.variables.implicitly_typed_list.value()) {
                if (contains(seenSoFar, v)) {
                    Variable sV;
                    sV.name = this->quantifiedIndexical.getPrefix()
                              + std::to_string(this->quantifiedIndexical.getNextIndex());
                    localSubst.insert(std::pair<Variable, Term>(v, sV));
                    // Replacement variables should contain new name for variable
                    replVariables.push_back(sV);
                } else {
                    // Not already replaced, this name is good
                    replVariables.push_back(v);
                }
            }
            // Apply the local subst
            Sentence subst = substVisitor.subst(localSubst,
                                                sentence.getQuantified());

            // Ensure all my existing and replaced variable
            // names are tracked
            seenSoFar.addAll(replVariables);

            Sentence sQuantified = (Sentence) subst.accept(this, arg);

            ForallSentence rs;
            rs.variables. = replVariables;
            rs

            return new QuantifiedSentence(sentence.getQuantifier(), replVariables,
                                          sQuantified);
        }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    struct RemoveQuantifiers
        : public boost::static_visitor<Sentence> {
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const { return s; }
        Sentence operator()(NotSentence s) const { return s; }

        Sentence operator()(ImplySentence s) const { return s; }
        Sentence operator()(ExistsSentence s) const { return s; }
        Sentence operator()(ForallSentence s) const { return s; }
    };

    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {
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

    struct CNFConstructor
        : public boost::static_visitor<Sentence> {
        Sentence operator()(Nil s) const { return s; }
        Sentence operator()(Literal<Term> s) const { return s; }
        Sentence operator()(ConnectedSentence s) const { return s; }
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
