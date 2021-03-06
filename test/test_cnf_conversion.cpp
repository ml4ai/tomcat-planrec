#define BOOST_TEST_MODULE TestCNF

#include "CNF.h"

#include <boost/test/included/unit_test.hpp>

#include <boost/variant/get.hpp>
#include <fstream>
#include <iostream>
#include <string>

#include "Clause.h"
#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/api.hpp"
#include "parsing/parse.hpp"
#include "util.h"
#include <boost/optional.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>

using boost::unit_test::framework::master_test_suite;
namespace x3 = boost::spirit::x3;
using namespace std;
using namespace ast;
using boost::get;

BOOST_AUTO_TEST_CASE(test_cnf_conversion) {
    // test the arguments conversion
    //  (or (b) (c) (d)) => (or (or (b) (c)) (d))
    auto a1 = parse<Sentence>("(or (b) (c) (d))");
    auto a2 = boost::apply_visitor(GeneratePairSentence(), a1);
    auto a3 = get<ConnectedSentence>(a2);
    BOOST_TEST(a3.connector == "or");
    auto a4 = get<ConnectedSentence>(a3.sentences[0]);
    auto a5 = get<Literal<Term>>(a4.sentences[0]);
    BOOST_TEST(a5.predicate == "b");
    auto a6 = get<Literal<Term>>(a4.sentences[1]);
    BOOST_TEST(a6.predicate == "c");
    auto a7 = get<Literal<Term>>(a3.sentences[1]);
    BOOST_TEST(a7.predicate == "d");

    //  (and (b) (c) (d)) => (and (and (b) (c)) (d))
    auto b1 = parse<Sentence>("(and (b) (c) (d))");
    auto b2 = boost::apply_visitor(GeneratePairSentence(), b1);
    auto b3 = get<ConnectedSentence>(b2);
    BOOST_TEST(b3.connector == "and");
    auto b4 = get<ConnectedSentence>(b3.sentences[0]);
    auto b5 = get<Literal<Term>>(b4.sentences[0]);
    BOOST_TEST(b5.predicate == "b");
    auto b6 = get<Literal<Term>>(b4.sentences[1]);
    BOOST_TEST(b6.predicate == "c");
    auto b7 = get<Literal<Term>>(b3.sentences[1]);
    BOOST_TEST(b7.predicate == "d");

    //  (or (a) (b) (and (c) (d) (e))) => (or (or (a) (b)) (and (and (c) (d))
    //  (e)))
    auto c1 = parse<Sentence>("(or (a) (b) (and (c) (d) (e)))");
    auto c2 = boost::apply_visitor(GeneratePairSentence(), c1);
    auto c3 = get<ConnectedSentence>(c2);
    BOOST_TEST(c3.connector == "or");
    auto c4 = get<ConnectedSentence>(c3.sentences[0]);
    BOOST_TEST(c4.connector == "or");
    auto c5 = get<Literal<Term>>(c4.sentences[0]);
    BOOST_TEST(c5.predicate == "a");
    auto c6 = get<Literal<Term>>(c4.sentences[1]);
    BOOST_TEST(c6.predicate == "b");
    auto c7 = get<ConnectedSentence>(c3.sentences[1]);
    BOOST_TEST(c7.connector == "and");
    auto c8 = get<ConnectedSentence>(c7.sentences[0]);
    auto c9 = get<Literal<Term>>(c8.sentences[0]);
    BOOST_TEST(c9.predicate == "c");
    auto c10 = get<Literal<Term>>(c7.sentences[1]);
    BOOST_TEST(c10.predicate == "e");

    // (or (a) (and (b) (c))) => (and (or (a) (b)) (or (a) (c)))
    auto d1 = parse<Sentence>("(or (a) (and (b) (c)))");
    auto d2 = boost::apply_visitor(DistributeOrOverAnd(), d1);
    auto d3 = get<ConnectedSentence>(d2);
    auto d4 = get<ConnectedSentence>(d3.sentences[0]);
    auto d5 = get<Literal<Term>>(d4.sentences[0]);
    BOOST_TEST(d5.predicate == "a");
    auto d6 = get<Literal<Term>>(d4.sentences[1]);
    BOOST_TEST(d6.predicate == "b");
    auto d7 = to_CNF(d1);
    BOOST_TEST(d7.conjunctionOfClauses[0].literals[0].predicate == "a");
    BOOST_TEST(d7.conjunctionOfClauses[0].literals[0].is_negative == false);
    BOOST_TEST(d7.conjunctionOfClauses[0].literals[1].predicate == "b");
    BOOST_TEST(d7.conjunctionOfClauses[0].literals[1].is_negative == false);

    // (or (and (a) (b)) (c)) => (and (or (a) (c)) (or (b) (c)))
    auto e1 = parse<Sentence>("(or (and (a) (b)) (not (c)))");
    auto e2 = boost::apply_visitor(DistributeOrOverAnd(), e1);
    auto e3 = get<ConnectedSentence>(e2);
    auto e4 = get<ConnectedSentence>(e3.sentences[0]);
    auto e5 = get<Literal<Term>>(e4.sentences[0]);
    BOOST_TEST(e5.predicate == "a");
    auto e6 = get<Literal<Term>>(get<NotSentence>(e4.sentences[1]).sentence);
    BOOST_TEST(e6.predicate == "c");
    auto e7 = to_CNF(e1);
    BOOST_TEST(e7.conjunctionOfClauses[0].literals[0].predicate == "a");
    BOOST_TEST(e7.conjunctionOfClauses[0].literals[0].is_negative == false);
    BOOST_TEST(e7.conjunctionOfClauses[0].literals[1].predicate == "c");
    BOOST_TEST(e7.conjunctionOfClauses[0].literals[1].is_negative == true);

    // (imply (a) (b)) => (or not (a) (b))
    auto f1 = parse<Sentence>("(imply (a) (b))");
    auto f2 = boost::apply_visitor(ImplicationsOut(), f1);
    auto f3 = get<ConnectedSentence>(f2);
    auto f4 = get<NotSentence>(f3.sentences[0]);
    auto f5 = get<Literal<Term>>(f4.sentence);
    BOOST_TEST(f5.predicate == "a");
    auto f6 = get<Literal<Term>>(f3.sentences[1]);
    BOOST_TEST(f6.predicate == "b");

    //  (forall (?y) (imply (A ?y) (L ?x ?y))) => (forall (?y) or not (A ?y) (L
    //  ?x ?y))
    auto g1 = parse<Sentence>("(forall (?y) (imply (A ?y) (L ?x ?y)))");
    auto g2 = boost::apply_visitor(ImplicationsOut(), g1);
    auto g3 = get<QuantifiedSentence>(g2);
    auto g4 = get<ConnectedSentence>(g3.sentence);
    auto g5 = get<NotSentence>(g4.sentences[0]);
    auto g6 = get<Literal<Term>>(g5.sentence);
    BOOST_TEST(g6.predicate == "A");
    auto g7 = get<Literal<Term>>(g4.sentences[1]);
    BOOST_TEST(g7.predicate == "L");

    //  (not (and (not (a)) (b))) => (or (a) (not (b)))
    auto h1 = parse<Sentence>("(not (and (not (a)) (b)))");
    auto h2 = boost::apply_visitor(NegationsIn(), h1);
    auto h3 = get<ConnectedSentence>(h2);
    BOOST_TEST(h3.connector == "or");
    auto h4 = get<Literal<Term>>(h3.sentences[0]);
    BOOST_TEST(h4.predicate == "a");
    auto h5 = get<NotSentence>(h3.sentences[1]);
    auto h6 = get<Literal<Term>>(h5.sentence);
    BOOST_TEST(h6.predicate == "b");

    //  (not (exists (?y) (and (not (A ?y)) (L ?x ?y)))) => (forall (?y) (or
    //  (A ?y) (not (L ?x ?y))))
    auto i1 =
        parse<Sentence>("(not (exists (?y) (and (not (A ?y)) (L ?x ?y))))");
    auto i2 = boost::apply_visitor(NegationsIn(), i1);
    auto i3 = get<QuantifiedSentence>(i2);
    BOOST_TEST(i3.variables.implicitly_typed_list[0].name == "y");
    auto i4 = get<ConnectedSentence>(i3.sentence);
    BOOST_TEST(i4.connector == "or");
    auto i5 = get<Literal<Term>>(i4.sentences[0]);
    BOOST_TEST(i5.predicate == "A");
    auto i6 = get<NotSentence>(i4.sentences[1]);
    auto i7 = get<Literal<Term>>(i6.sentence);
    BOOST_TEST(i7.predicate == "L");

    // (or (exists (?x) (Q ?x ? z)) (forall (?x) (P ?x ?y))) => (or (exists
    // (?x) (Q ?x ? z)) (forall (?q0) (P ?x ?y)))
    auto j1 = parse<Sentence>(
        "(or (exists (?x) (Q ?x ? z)) (forall (?x) (P ?x ?y)))");
    auto j2 =
        boost::apply_visitor(StandardizeQuantiferVariables(), (Sentence)j1);
    auto j3 = get<ConnectedSentence>(j2);
    auto j4 = get<QuantifiedSentence>(j3.sentences[0]);
    BOOST_TEST(j4.quantifier == "exists");
    BOOST_TEST(j4.variables.implicitly_typed_list[0].name == "x");
    auto j5 = get<QuantifiedSentence>(j3.sentences[1]);
    BOOST_TEST(j5.quantifier == "forall");
    BOOST_TEST(j5.variables.implicitly_typed_list[0].name == "q0");

    //  (or (exists (?w) (forall (?z) (Q ?w ? z))) (exists (?w) (exists (?z) (Q
    //  ?w ? z)))) => (or (exists (?w) (forall (?z) (Q ?w ? z))) (exists (?q0)
    //  (exists (?q1) (Q ?w ? z))))
    auto k1 = parse<Sentence>("(or (exists (?w) (forall (?z) (Q ?w ? z))) "
                              "(exists (?w) (exists (?z) (Q ?w ? z))))");
    auto k2 =
        boost::apply_visitor(StandardizeQuantiferVariables(), (Sentence)k1);
    auto k3 = get<ConnectedSentence>(k2);
    auto k4 = get<QuantifiedSentence>(k3.sentences[0]);
    BOOST_TEST(k4.quantifier == "exists");
    BOOST_TEST(k4.variables.implicitly_typed_list[0].name == "w");
    auto k5 = get<QuantifiedSentence>(k4.sentence);
    BOOST_TEST(k5.quantifier == "forall");
    BOOST_TEST(k5.variables.implicitly_typed_list[0].name == "z");

    auto k6 = get<QuantifiedSentence>(k3.sentences[1]);
    BOOST_TEST(k6.quantifier == "exists");
    BOOST_TEST(k6.variables.implicitly_typed_list[0].name == "q0");
    auto k7 = get<QuantifiedSentence>(k6.sentence);
    BOOST_TEST(k7.quantifier == "exists");
    BOOST_TEST(k7.variables.implicitly_typed_list[0].name == "q1");

    // (exists (?w) (forall (?z) (Q ?w ? z))) => (Q ?SC0 ?z)
    FOLDomain domain;
    domain.addPredicate("Q");
    auto l1 = parse<Sentence>("(exists (?w) (forall (?z) (Q ?w ? z)))");
    auto l2 = to_CNF(l1, domain);
    BOOST_TEST(l2.conjunctionOfClauses[0].literals[0].predicate == "Q");
    BOOST_TEST(get<Variable>(l2.conjunctionOfClauses[0].literals[0].args[0]).name == "SC0");
    BOOST_TEST(get<Variable>(l2.conjunctionOfClauses[0].literals[0].args[1]).name == "z");
    BOOST_TEST(l2.conjunctionOfClauses[0].literals[0].is_negative == false);
}

BOOST_AUTO_TEST_CASE(test_custom_map) {
    std::unordered_map<Variable, Symbol, Hash<Variable>> mymap;
    auto v = Variable{"var"};
    mymap[v] =  Symbol{"sym"};
    BOOST_TEST(mymap.contains(v));
    std::vector<Variable> myvec;
    auto v1 = Variable{"var1"};
    auto v2 = Variable{"var2"};
    myvec.push_back(v);
    myvec.push_back(v1);

    auto tmp = std::find(myvec.begin(), myvec.end(), v) != myvec.end();
    BOOST_TEST(in(v, myvec));
    BOOST_TEST(in(v2, myvec) == false);
}
