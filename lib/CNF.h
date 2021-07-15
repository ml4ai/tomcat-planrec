#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "fol/Function.h"
#include "parsing/ast.hpp"
#include <iostream>
#include <map>
#include <typeinfo>
#include <utility>
#include <unordered_map>

using boost::get;
using namespace std;

namespace ast {
    bool vector_contains_variable(std::vector<Variable> v, Variable x) {
        for (auto & i : v){
            if (i == x){
                return true;
            }
        }
        return false;
    }
    bool map_contains_variable(std::unordered_map<Variable, Symbol> m, Variable x) {
        for (const auto& [key, value] : m) {
            if (key == x){
                return true;
            }
        }
        return false;
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
        std::string getPrefix() { return "q"; }
        int getNextIndex() { return this->index++; }
    };

//    struct SubstVisitor : public boost::static_visitor<Sentence> {
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta,
////                            Sentence s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, Nil s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);;
////        }
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, Literal<Term> s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, ConnectedSentence s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, NotSentence s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, ImplySentence s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, ExistsSentence s) const {
////            return boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////        Sentence operator()(std::unordered_map<Variable, Symbol> theta, ForallSentence s) const {
////
////        }
//
////        Symbol operator()(std::unordered_map<Variable, Symbol> theta,
////                          Symbol s) const {
////            return (Symbol)boost::apply_visitor(SubstVisitor(), s, theta);
////        }
////        fol::Function operator()(std::unordered_map<Variable, Symbol> theta,
////                                 fol::Function s) const {
////            return (fol::Function)boost::apply_visitor(
////                SubstVisitor(), s, theta);
////        }
////        Literal<Term> operator()(std::unordered_map<Variable, Symbol> theta,
////                                 Literal<Term> s) const {
////            return (Literal<Term>)boost::apply_visitor(
////                SubstVisitor(), s, theta);
////        }
//
//        Variable operator()(Variable s, std::unordered_map<Variable, Symbol> theta) const {
//            std::unordered_map<Variable, Symbol> substitution(std::move(theta));
//            Variable rs;
//            if (map_contains_variable(substitution, s)) {
//                rs.name = substitution.find(s)->second.name;
//                return rs;
//            }
//            rs.name = s.name;
//            return rs;
//        }
//
//        Sentence operator()(ForallSentence s,
//                            std::unordered_map<Variable, Symbol> theta) const {
//            std::unordered_map<Variable, Symbol> substitution(std::move(theta));
//            auto quantifiedAfterSubs =
//                boost::apply_visitor(SubstVisitor(), (Sentence)s.sentence, theta);
//
//            std::vector<Variable> variables;
//            for (auto v : s.variables.implicitly_typed_list.value()) {
//                if (map_contains_variable(substitution, v)) {
//                    Symbol st = substitution.find(v)->second;
//                    if (typeid(st) == typeid(Variable)){
//                        Variable rs;
//                        rs.name = st.name;
//                        variables.push_back(rs);
//                    }
//                }
//                else {
//                    Variable rs;
//                    rs.name = v.name;
//                    variables.push_back(rs);
//                }
//            }
//            if (variables.empty()) {
//                return quantifiedAfterSubs;
//            }
//
//            ForallSentence rs;
//            for (const auto& variable : variables) {
//                rs.variables.implicitly_typed_list.value().push_back(variable);
//            }
//            rs.sentence = quantifiedAfterSubs;
//            return rs;
//        }
//
//        Sentence operator()(ExistsSentence s,
//                            std::unordered_map<Variable, Symbol> theta) const {
//            std::unordered_map<Variable, Symbol> substitution(std::move(theta));
//            auto quantifiedAfterSubs =
//                boost::apply_visitor(SubstVisitor(), s.sentence, theta);
//
//            std::vector<Variable> variables;
//            for (auto v : s.variables.implicitly_typed_list.value()) {
//                if (map_contains_variable(substitution, v)) {
//                    Symbol st = substitution.find(v)->second;
//                    if (typeid(st) == typeid(Variable)){
//                        Variable rs;
//                        rs.name = st.name;
//                        variables.push_back(rs);
//                    }
//                }
//                else {
//                    Variable rs;
//                    rs.name = v.name;
//                    variables.push_back(rs);
//                }
//            }
//            if (variables.empty()) {
//                return quantifiedAfterSubs;
//            }
//
//            ExistsSentence rs;
//            for (const auto& variable : variables) {
//                rs.variables.implicitly_typed_list.value().push_back(variable);
//            }
//            rs.sentence = quantifiedAfterSubs;
//            return rs;
//        }
//
//        Sentence operator()(Nil s, std::unordered_map<Variable, Symbol> theta) const { return s; }
//        Sentence operator()(Literal<Term> s, std::unordered_map<Variable, Symbol> theta) const { return s; }
//        Sentence operator()(ConnectedSentence s, std::unordered_map<Variable, Symbol> theta) const {
//            auto s1 = boost::apply_visitor(SubstVisitor(),
//                                           (Sentence)s.sentences[0], theta);
//            auto s2 = boost::apply_visitor(SubstVisitor(),
//                                           (Sentence)s.sentences[1], theta);
//            ConnectedSentence rs;
//            rs.connector = s.connector;
//            rs.sentences.push_back(s1);
//            rs.sentences.push_back(s2);
//            return rs;
//        }
//        Sentence operator()(NotSentence s, std::unordered_map<Variable, Symbol> theta) const {
//            NotSentence rs;
//            rs.sentence = boost::apply_visitor(SubstVisitor(),
//                                               (Sentence)s.sentence, theta);
//            return rs;
//        }
//        Sentence operator()(ImplySentence s, std::unordered_map<Variable, Symbol> theta) const {
//            auto s1 = boost::apply_visitor(SubstVisitor(),
//                                           (Sentence)s.sentence1, theta);
//            auto s2 = boost::apply_visitor(SubstVisitor(),
//                                           (Sentence)s.sentence2, theta);
//            ImplySentence rs;
//            rs.sentence1 = s1;
//            rs.sentence2 = s2;
//            return rs;
//        }
//    };
//
//    struct StandardizeQuantiferVariables
//        : public boost::static_visitor<Sentence> {
//        StandardizeApartIndexical quantifiedIndexical;
//        int i = quantifiedIndexical.getNextIndex();
//
//        Sentence operator()(Nil s, vector<Variable> arg) const { return s; }
//        Sentence operator()(Literal<Term> s, vector<Variable> arg) const {
//            return s;
//        }
//        Sentence operator()(ConnectedSentence s, vector<Variable> arg) const {
//            auto s1 = boost::apply_visitor(StandardizeQuantiferVariables(),
//                                           (Sentence)s.sentences[0]);
//            auto s2 = boost::apply_visitor(StandardizeQuantiferVariables(),
//                                           (Sentence)s.sentences[1]);
//            ConnectedSentence rs;
//            rs.connector = s.connector;
//            rs.sentences.push_back(s1);
//            rs.sentences.push_back(s2);
//            return rs;
//        }
//        Sentence operator()(NotSentence s, vector<Variable> arg) const {
//            NotSentence rs;
//            rs.sentence = boost::apply_visitor(StandardizeQuantiferVariables(),
//                                               (Sentence)s.sentence);
//            return rs;
//        }
//
//        Sentence operator()(ImplySentence s, vector<Variable> arg) const {
//            auto s1 = boost::apply_visitor(StandardizeQuantiferVariables(),
//                                           (Sentence)s.sentence1);
//            auto s2 = boost::apply_visitor(StandardizeQuantiferVariables(),
//                                           (Sentence)s.sentence2);
//            ImplySentence rs;
//            rs.sentence1 = s1;
//            rs.sentence2 = s2;
//            return rs;
//        }
//        // can't be constant
//        Sentence operator()(ExistsSentence s, vector<Variable> arg) {
//            vector<Variable> seenSoFar = arg;
//            std::unordered_map<Variable, Symbol> localSubst;
//            std::vector<Variable> replVariables;
//            for (auto v : s.variables.implicitly_typed_list.value()) {
//                if (vector_contains_variable(seenSoFar, v)) {
//                    Variable sV;
//                    sV.name = this->quantifiedIndexical.getPrefix() +
//                              std::to_string(
//                                  this->quantifiedIndexical.getNextIndex());
//                    localSubst.insert({v, sV});
//                    // Replacement variables should contain new name for
//                    // variable
//                    replVariables.push_back(sV);
//                }
//                else {
//                    // Not already replaced, this name is good
//                    replVariables.push_back(v);
//                }
//            }
//            // Apply the local subst
//            auto subst = boost::apply_visitor(
//                SubstVisitor(), s.sentence, localSubst);
//            //            Sentence subst = substVisitor.subst(localSubst,
//            //                                                sentence.getQuantified());
//
//            // Ensure all my existing and replaced variable
//            // names are tracked
//            for (const auto & replVariable : replVariables){
//                seenSoFar.push_back(replVariable);
//            }
//
//            auto sQuantified = boost::apply_visitor(
//                StandardizeQuantiferVariables(), localSubst, subst);
//
//            ExistsSentence rs;
//            for (const auto & replVariable : replVariables){
//                rs.variables.implicitly_typed_list.value().push_back(replVariable);
//            }
//            rs.sentence = sQuantified;
//
//            return rs;
//        }
//        Sentence operator()(ForallSentence s, vector<Variable> arg) {
//            vector<Variable> seenSoFar = arg;
//            std::unordered_map<Variable, Symbol> localSubst;
//            std::vector<Variable> replVariables;
//            for (auto v : s.variables.implicitly_typed_list.value()) {
//                if (vector_contains_variable(seenSoFar, v)) {
//                    Variable sV;
//                    sV.name = this->quantifiedIndexical.getPrefix() +
//                              std::to_string(
//                                  this->quantifiedIndexical.getNextIndex());
//                    localSubst.insert({v, sV});
//                    // Replacement variables should contain new name for
//                    // variable
//                    replVariables.push_back(sV);
//                }
//                else {
//                    // Not already replaced, this name is good
//                    replVariables.push_back(v);
//                }
//            }
//            // Apply the local subst
//            auto subst = boost::apply_visitor(
//                SubstVisitor(), localSubst, (Sentence)s.sentence);
//            //            Sentence subst = substVisitor.subst(localSubst,
//            //                                                sentence.getQuantified());
//
//            // Ensure all my existing and replaced variable
//            // names are tracked
//            for (const auto & replVariable : replVariables){
//                seenSoFar.push_back(replVariable);
//            }
//
//            auto sQuantified = boost::apply_visitor(
//                StandardizeQuantiferVariables(), localSubst, subst);
//
//            ForallSentence rs;
//            for (const auto & replVariable : replVariables){
//                rs.variables.implicitly_typed_list.value().push_back(replVariable);
//            }
//            rs.sentence = sQuantified;
//
//            return rs;
//        }
//    };

    struct RemoveQuantifiers : public boost::static_visitor<Sentence> {
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

    struct ArgData {
      std::vector<Clause> clauses;
      bool negated = false;
      ArgData() {
          Clause c;
          clauses.push_back(c);
      }
    };

    using Arg = boost::variant<ArgData>;

    struct CNF {

      std::vector<Clause> conjunctionOfClauses;

      explicit CNF(const std::vector<Clause>& conjunctionOfClauses) {
          for (const auto & conjunctionOfClause : conjunctionOfClauses){
              this->conjunctionOfClauses.push_back(conjunctionOfClause);
          }
      }

      int getNumberOfClauses() const {
            return this->conjunctionOfClauses.size();
        }

      std::vector<Clause> getConjunctionOfClauses() const {
            return this->conjunctionOfClauses;
        }
    };

    struct CNFConstructor : public boost::static_visitor<Sentence> {
        CNF construct(Sentence orDistributedOverAnd){
            ArgData ad = ArgData();
            boost::apply_visitor(CNFConstructor(), (Sentence)orDistributedOverAnd, (Arg)ad);
            CNF c= CNF(ad.clauses);
            return c;
        }

        Sentence operator()(Nil s, ArgData ad) const { return s; }
        Sentence operator()(Literal<Term> s, ArgData ad) const {
            ArgData ad_ = std::move(ad);
            ad_.clauses[ad_.clauses.size() - 1].literals.push_back(s);
            return s;
        }
        Sentence operator()(ConnectedSentence s, ArgData ad) const {
            ArgData ad_ = ad;
            boost::apply_visitor(CNFConstructor(), s.sentences[0], (Arg)ad);
            if (s.connector == "and"){
                Clause c;
                ad_.clauses.push_back(c);
            }
            boost::apply_visitor(CNFConstructor(), s.sentences[1], (Arg)ad);
            return s;
        }
        Sentence operator()(NotSentence s, ArgData ad) const {
            ArgData ad_ = ad;
            ad_.negated = true;
            boost::apply_visitor(CNFConstructor(), s.sentence, (Arg)ad);
            ad_.negated = false;
            return s;
        }

        Sentence operator()(ImplySentence s, ArgData ad) const { return s; }
        Sentence operator()(ExistsSentence s, ArgData ad) const { return s; }
        Sentence operator()(ForallSentence s, ArgData ad) const { return s; }
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
