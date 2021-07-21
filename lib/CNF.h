#pragma once

#include "Clause.h"
#include "boost/variant.hpp"
#include "fol/Function.h"
#include "parsing/ast.hpp"
#include <iostream>
#include <map>
#include <typeinfo>
#include <unordered_map>
#include <utility>
#include <boost/throw_exception.hpp>

namespace ast {
    bool vector_contains_variable(std::vector<Variable> v, Variable x) {
        for (auto& i : v) {
            if (i == x) {
                return true;
            }
        }
        return false;
    }
    // Custom hash
    template <class T> struct Hash {
        std::size_t operator()(T const& x) const noexcept {
            return std::hash<std::string>{}(x.name);
        }
    };

    bool map_contains_variable(std::unordered_map<Variable, Symbol> m,
                               Variable x) {
        for (const auto& [key, value] : m) {
            if (key == x) {
                return true;
            }
        }
        return false;
    }

    template <class Visitor, class T> auto visit(T x) {
        return boost::apply_visitor(Visitor(), x);
    }

    template <class Visitor>
    std::vector<Sentence> visit(std::vector<Sentence> sentences) {
        std::vector<Sentence> transformed_sentences = {};
        for (auto s : sentences) {
            transformed_sentences.push_back(visit<Visitor>((Sentence)s));
        }
        return transformed_sentences;
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
        std::string operator()(QuantifiedSentence s) const {
            return "QuantifiedSentence";
        }
        std::string operator()(EqualsSentence s) const {
            return "EqualsSentence";
        }
    };

    using args = boost::variant<fol::Constant, fol::Variable, fol::Function>;
    struct GetArgType : public boost::static_visitor<std::string> {
        std::string operator()(fol::Constant s) const {
            return "Constant";
        }
        std::string operator()(fol::Variable s) const {
            return "Variable";
        }
        std::string operator()(fol::Function s) const {
            return "Function";
        }
    };

    struct GeneratePairSentence : public boost::static_visitor<Sentence> {

        // For connected sentences (and/or sentences), we generate pairs.
        Sentence operator()(ConnectedSentence s) const {
            auto rs = ConnectedSentence{s.connector};
            if (s.sentences.size() <= 2) {
                for (auto sentence : s.sentences) {
                    rs.sentences.push_back(
                        visit<GeneratePairSentence>(Sentence(sentence)));
                }
                return rs;
            }

            auto last_sen = s.sentences.back();
            s.sentences.pop_back();
            rs.sentences.push_back(visit<GeneratePairSentence>((Sentence)s));
            rs.sentences.push_back(
                visit<GeneratePairSentence>((Sentence)last_sen));
            return rs;
        }

        // For all other sentences, we return the sentence unchanged.
        template <class T> Sentence operator()(T s) const { return s; }
    };

    struct ImplicationsOut : public boost::static_visitor<Sentence> {
        Sentence operator()(ConnectedSentence s) const {
            return ConnectedSentence{s.connector,
                                     visit<ImplicationsOut>(s.sentences)};
        }
        Sentence operator()(ImplySentence s) const {
            auto s1 = visit<ImplicationsOut>((Sentence)s.sentence1);
            auto s2 = visit<ImplicationsOut>((Sentence)s.sentence2);

            NotSentence rs1{s1};
            return ConnectedSentence{"or", {rs1, s2}};
        }
        Sentence operator()(QuantifiedSentence s) const {
            QuantifiedSentence rs{s.quantifier,
                                  s.variables,
                                  visit<ImplicationsOut>((Sentence)s.sentence)};
            return rs;
        }
        Sentence operator()(EqualsSentence s) const {
            BOOST_THROW_EXCEPTION(std::runtime_error("EqualsSentence handling not yet implemented!"));
        }

        template <class T> Sentence operator()(T s) const { return s; }
    };

    struct NegationsIn : public boost::static_visitor<Sentence> {
        Sentence operator()(ConnectedSentence s) const {
            return ConnectedSentence{s.connector,
                                     visit<NegationsIn>(s.sentences)};
        }
        Sentence operator()(NotSentence s) const {
            auto s1 = s.sentence;
            if (visit<GetSentenceType>((Sentence)s1) == "NotSentence") {
                auto s_ = get<NotSentence>(s1);
                return visit<NegationsIn>((Sentence)s_.sentence);
            }

            if (visit<GetSentenceType>((Sentence)s1) == "ConnectedSentence") {
                auto s_ = get<ConnectedSentence>(s1);
                auto s_1 = s_.sentences[0];
                auto s_2 = s_.sentences[1];
                ConnectedSentence rs;
                rs.connector = (s_.connector == "and") ? "or" : "and";
                NotSentence rs1{s_1};
                NotSentence rs2{s_2};
                rs.sentences = visit<NegationsIn>({rs1, rs2});
                return rs;
            }

            if (visit<GetSentenceType>((Sentence)s1) == "QuantifiedSentence") {
                auto s_ = get<QuantifiedSentence>(s1);
                NotSentence rs1{s_.sentence};

                std::string quantifier =
                    (s_.quantifier == "forall") ? "exists" : "forall";
                QuantifiedSentence rs{quantifier,
                                      s_.variables,
                                      visit<NegationsIn>((Sentence)rs1)};
                return rs;
            }

            NotSentence rs{visit<NegationsIn>((Sentence)s1)};
            return rs;
        }
        Sentence operator()(ImplySentence s) const {
            auto s1 = visit<NegationsIn>((Sentence)s.sentence1);
            auto s2 = visit<NegationsIn>((Sentence)s.sentence2);

            ImplySentence rs{s1, s2};
            return rs;
        }
        Sentence operator()(QuantifiedSentence s) const {
            return QuantifiedSentence{s.quantifier,
                                      s.variables,
                                      visit<NegationsIn>((Sentence)s.sentence)};
        }

        template <class T> Sentence operator()(T s) const { return s; }
    };

    struct StandardizeApartIndexical {
        int index = 0;
        std::string getPrefix() { return "q"; }
        int getNextIndex() { return this->index++; }
    };

    struct SubstVisitor : public boost::static_visitor<Sentence>, public boost::static_visitor<Term>{
        std::unordered_map<Variable, Symbol, Hash<Variable>> theta;

        Term operator()(Variable s) const {
            if (this->theta.contains(s)) {
//                return Symbol{this->theta.at(s).name};
                return Variable{this->theta.at(s).name};
//                return this->theta.at(s).name;
            }
            return Variable{s.name};
//            return s.name;
        }

        Term operator()(Constant s) const {
            return s;
        }

        Term operator()(fol::Function s) const {
            return s;
        }

        Sentence operator()(Literal<Term> s) const {
            if (!s.args.empty()) {
                for (int i=0; i <s.args.size(); i++) {
                    if (visit<GetArgType>((Term)s.args[i]) == "Variable"){
                        get<Variable>(s.args[i]).name = get<Variable>(boost::apply_visitor(*this, s.args[i])).name;
                    }
                }
            }
//            return visit(*this, s);
            return s;
        }

        Sentence operator()(QuantifiedSentence s) const {
            auto quantifiedAfterSubs =
                    boost::apply_visitor(*this, (Sentence)s.sentence);

            std::vector<Variable> variables;
            for (auto v : s.variables.implicitly_typed_list.value()) {
                if (this->theta.contains(v)){
                    Symbol st = this->theta.at(v);
                    if (typeid(st) == typeid(Variable)) {
                        Variable rs;
                        rs.name = st.name;
                        variables.push_back(rs);
                    }
                }
                else {
                    Variable rs;
                    rs.name = v.name;
                    variables.push_back(rs);
                }
            }
            if (variables.empty()) {
                return quantifiedAfterSubs;
            }

            QuantifiedSentence rs;
            rs.quantifier = s.quantifier;
            for (const auto & variable : variables){
                rs.variables.implicitly_typed_list.value().push_back(variable);
            }
            rs.sentence = quantifiedAfterSubs;

            return rs;
        }
        Sentence operator()(EqualsSentence s) const {
            BOOST_THROW_EXCEPTION(std::runtime_error("EqualsSentence handling not yet implemented!"));
        }

        template <class T> Sentence operator()(T s) const { return s; }
    };

    //    struct StandardizeQuantiferVariables
    //        : public boost::static_visitor<Sentence> {
    //        StandardizeApartIndexical quantifiedIndexical;
    //        int i = quantifiedIndexical.getNextIndex();
    //
    //        Sentence operator()(Nil s, vector<Variable> arg) const { return s;
    //        } Sentence operator()(Literal<Term> s, vector<Variable> arg) const
    //        {
    //            return s;
    //        }
    //        Sentence operator()(ConnectedSentence s, vector<Variable> arg)
    //        const {
    //            auto s1 =
    //            visit<StandardizeQuantiferVariables(),
    //                                           (Sentence)s.sentences[0]);
    //            auto s2 =
    //            visit<StandardizeQuantiferVariables(),
    //                                           (Sentence)s.sentences[1]);
    //            ConnectedSentence rs;
    //            rs.connector = s.connector;
    //            rs.sentences.push_back(s1);
    //            rs.sentences.push_back(s2);
    //            return rs;
    //        }
    //        Sentence operator()(NotSentence s, vector<Variable> arg) const {
    //            NotSentence rs;
    //            rs.sentence =
    //            visit<StandardizeQuantiferVariables(),
    //                                               (Sentence)s.sentence);
    //            return rs;
    //        }
    //
    //        Sentence operator()(ImplySentence s, vector<Variable> arg) const {
    //            auto s1 =
    //            visit<StandardizeQuantiferVariables(),
    //                                           (Sentence)s.sentence1);
    //            auto s2 =
    //            visit<StandardizeQuantiferVariables(),
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
    //            auto subst = visit<
    //                SubstVisitor(), s.sentence, localSubst);
    //            //            Sentence subst = substVisitor.subst(localSubst,
    //            // sentence.getQuantified());
    //
    //            // Ensure all my existing and replaced variable
    //            // names are tracked
    //            for (const auto & replVariable : replVariables){
    //                seenSoFar.push_back(replVariable);
    //            }
    //
    //            auto sQuantified = visit<
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
    //            auto subst = visit<
    //                SubstVisitor(), localSubst, (Sentence)s.sentence);
    //            //            Sentence subst = substVisitor.subst(localSubst,
    //            // sentence.getQuantified());
    //
    //            // Ensure all my existing and replaced variable
    //            // names are tracked
    //            for (const auto & replVariable : replVariables){
    //                seenSoFar.push_back(replVariable);
    //            }
    //
    //            auto sQuantified = visit<
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
        Sentence operator()(QuantifiedSentence s) const { return s; }
        Sentence operator()(EqualsSentence s) const { return s; }
    };

    struct DistributeOrOverAnd : public boost::static_visitor<Sentence> {

        Sentence operator()(ConnectedSentence s) const {
            auto s1 = visit<DistributeOrOverAnd>(s.sentences[0]);
            auto s2 = visit<DistributeOrOverAnd>(s.sentences[1]);

            if (s.connector == "or") {
                ConnectedSentence rs{"and"};
                if (visit<GetSentenceType>(s2) == "ConnectedSentence") {
                    auto s2_ = get<ConnectedSentence>(s2);
                    if (s2_.connector == "and") {
                        auto s2_1 = s2_.sentences[0];
                        auto s2_2 = s2_.sentences[1];
                        ConnectedSentence rs1{"or", {s1, s2_1}};
                        ConnectedSentence rs2{"or", {s1, s2_2}};
                        rs.sentences = visit<DistributeOrOverAnd>({rs1, rs2});
                        return rs;
                    }
                }

                if (visit<GetSentenceType>(s1) == "ConnectedSentence") {
                    auto s1_ = get<ConnectedSentence>(s1);
                    if (s1_.connector == "and") {
                        auto s1_1 = s1_.sentences[0];
                        auto s1_2 = s1_.sentences[1];
                        ConnectedSentence rs1{"or", {s1_1, s2}};
                        ConnectedSentence rs2{"or", {s1_2, s2}};
                        rs.sentences = visit<DistributeOrOverAnd>({rs1, rs2});
                        return rs;
                    }
                }
            }

            return ConnectedSentence{s.connector, {s1, s2}};
        }

        template <class T> Sentence operator()(T s) const { return s; }
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
            for (const auto& conjunctionOfClause : conjunctionOfClauses) {
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

    struct CNFConstructor : public boost::static_visitor<> {
        ArgData ad = ArgData();
        void operator()(Nil& s) {}
        void operator()(Literal<Term>& s) {
            this->ad.clauses[this->ad.clauses.size() - 1].literals.push_back(s);
        }
        void operator()(ConnectedSentence& s) {
            boost::apply_visitor(*this, s.sentences[0]);
            if (s.connector == "and") {
                Clause c;
                this->ad.clauses.push_back(c);
            }
            boost::apply_visitor(*this, s.sentences[1]);
        }
        void operator()(NotSentence& s) {
            if (boost::apply_visitor(GetSentenceType(), s.sentence) ==
                "Literal") {
                get<Literal<Term>>(s.sentence).is_negative = true;
            }
            boost::apply_visitor(*this, s.sentence);
        }

        void operator()(ImplySentence& s) {
            BOOST_THROW_EXCEPTION(std::runtime_error(
                "All imply sentences should already have been removed."));
        }
        void operator()(QuantifiedSentence& s) {
            BOOST_THROW_EXCEPTION(std::runtime_error(
                "All quantified sentences should already have been removed."));
        }
        void operator()(EqualsSentence& s) {
            BOOST_THROW_EXCEPTION(std::runtime_error(
                "EqualsSentence handling not yet implemented!"));
        }

    };

    CNF construct(Sentence orDistributedOverAnd) {
        auto cnf_constructor = CNFConstructor();
        boost::apply_visitor(cnf_constructor, orDistributedOverAnd);
        CNF c(cnf_constructor.ad.clauses);
        return c;
    }

    Sentence to_CNF(Sentence s) {
        //        auto visitor1 = GeneratePairSentence();
        auto s1 = visit<GeneratePairSentence>(s);
        //        auto visitor2 = DistributeOrOverAnd();
        //        auto s2 = get<ConnectedSentence>(s1);
        //        auto s3 =
        //        get<ConnectedSentence>(get<ConnectedSentence>(s2.sentences[1]).sentences[0]);
        //        return visit<DistributeOrOverAnd>(s1);
    }
} // namespace ast
