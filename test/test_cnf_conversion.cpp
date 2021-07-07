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
