#define BOOST_TEST_MODULE TestCNF


#include "CNF.h"

#include <boost/test/included/unit_test.hpp>

#include <boost/variant/get.hpp>
#include <fstream>
#include <iostream>
#include <string>

#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/domain.hpp"
#include "parsing/parse.hpp"
#include "util.h"
#include "Clause.h"
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
    auto a1 = parse<Sentence>("(or (b) (c) (d))", sentence());
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
    auto b1 = parse<Sentence>("(and (b) (c) (d))", sentence());
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

    //  (or (a) (b) (and (c) (d) (e))) => (or (or (a) (b)) (and (and (c) (d)) (e)))
    auto c1 = parse<Sentence>("(or (a) (b) (and (c) (d) (e)))", sentence());
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
    auto d1 = parse<Sentence>("(or (a) (and (b) (c)))", sentence());
    auto d2 = boost::apply_visitor(DistributeOrOverAnd(), d1);
    auto d3 = get<ConnectedSentence>(d2);
    auto d4 = get<ConnectedSentence>(d3.sentences[0]);
    auto d5 = get<Literal<Term>>(d4.sentences[0]);
    BOOST_TEST(d5.predicate == "a");
    auto d6 = get<Literal<Term>>(d4.sentences[1]);
    BOOST_TEST(d6.predicate == "b");

    // (or (and (a) (b)) (c)) => (and (or (a) (c)) (or (b) (c)))
    auto e1 = parse<Sentence>("(or (and (a) (b)) (c))", sentence());
    auto e2 = boost::apply_visitor(DistributeOrOverAnd(), e1);
    auto e3 = get<ConnectedSentence>(e2);
    auto e4 = get<ConnectedSentence>(e3.sentences[0]);
    auto e5 = get<Literal<Term>>(e4.sentences[0]);
    BOOST_TEST(e5.predicate == "a");
    auto e6 = get<Literal<Term>>(e4.sentences[1]);
    BOOST_TEST(e6.predicate == "c");

    // (imply (a) (b)) => (or not (a) (b))
    auto f1 = parse<Sentence>("(imply (a) (b))", sentence());
    auto f2 = boost::apply_visitor(ImplicationsOut(), f1);
    auto f3 = get<ConnectedSentence>(f2);
    auto f4 = get<NotSentence>(f3.sentences[0]);
    auto f5 = get<Literal<Term>>(f4.sentence);
    BOOST_TEST(f5.predicate == "a");
    auto f6 = get<Literal<Term>>(f3.sentences[1]);
    BOOST_TEST(f6.predicate == "b");

    //  (forall (?y) (imply (A ?y) (L ?x ?y))) => (forall (?y) or not (A ?y) (L ?x ?y))
    auto g1 = parse<Sentence>("(forall (?y) (imply (A ?y) (L ?x ?y)))", sentence());
    auto g2 = boost::apply_visitor(ImplicationsOut(), g1);
    auto g3 = get<ForallSentence>(g2);
    auto g4 = get<ConnectedSentence>(g3.sentence);
    auto g5 = get<NotSentence>(g4.sentences[0]);
    auto g6 = get<Literal<Term>>(g5.sentence);
    BOOST_TEST(g6.predicate == "A");
    auto g7 = get<Literal<Term>>(g4.sentences[1]);
    BOOST_TEST(g7.predicate == "L");

    auto h1 = parse<Sentence>("(not (not (a)))", sentence());
    auto h2 = boost::apply_visitor(NegationsIn(), h1);
    auto h3 = get<Literal<Term>>(h2);
    BOOST_TEST(h3.predicate == "a");

//    //  (not (and (not (a)) (b))) => (or (a) (not (b)))
//    auto h1 = parse<Sentence>("(not (and (not (a)) (b)))", sentence());
//    auto h2 = boost::apply_visitor(NegationsIn(), h1);
//    auto h3 = get<ConnectedSentence>(h2);
//    BOOST_TEST(h3.connector == "or");
//    auto h4 = get<NotSentence>(h3.sentences[0]);
//    auto h5 = get<Literal<Term>>(h4.sentence);
//    BOOST_TEST(h5.predicate == "a");
//    auto h6 = get<NotSentence>(h3.sentences[1]);
//    auto h7 = get<Literal<Term>>(h6.sentence);
//    BOOST_TEST(h7.predicate == "b");

//     (not (exists (?y) (and (not (A ?y)) (L ?x ?y)))) => (forall (?y) (or (A ?y) (not (L ?x ?y))))
//    auto h1 = parse<Sentence>("(not (exists (?y) (and (not (A ?y)) (L ?x ?y)))", sentence());
//    auto h2 = boost::apply_visitor(NegationsIn(), h1);
//    auto h3 = get<ForallSentence>(h2);
//    BOOST_TEST(h3.variables.implicitly_typed_list.value()[0].name ==
//               "y");
//    auto h4 = get<ConnectedSentence>(h3.sentence);
//    BOOST_TEST(h4.connector == "or");
//    auto h5 = get<Literal<Term>>(h4.sentences[0]);
//    BOOST_TEST(h5.predicate == "A");
//    auto h6 = get<NotSentence>(h4.sentences[1]);
//    auto h7 = get<Literal<Term>>(h6.sentence);
//    BOOST_TEST(h7.predicate == "L");

    //  test imply
//    auto s1 =
//        parse<Sentence>("(imply (Animal ?y) (Loves ?x ?y))", sentence());

//    auto s1 = parse<ast::Sentence>("(predicate c1 c2)", sentence());
//    auto s2 = parse<Sentence>("(or (a) (and (b) (c) (d)))", sentence());
//
//    // Should produce (a ∨ b) ∧ (a ∨ c)
//    auto clauses = to_CNF(s2);
//    cout << endl;

    // THIS TEST FAILS, FIXME
//    BOOST_TEST(get<ast::AtomicFormula<ast::Term>>(clauses[0].literals[0]).predicate.name == "a");
}
