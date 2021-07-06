#define BOOST_TEST_MODULE TestUnification

#include <boost/test/included/unit_test.hpp>
#include <vector>
#include "unification.h"
#include <iostream>
#include "fol/Variable.h"
#include "fol/Constant.h"
#include "fol/Literal.h"
#include "fol/Term.h"
#include "fol/Function.h"
#include "Visitor.h"
#include "boost/variant.hpp"

#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/domain.hpp"
#include "parsing/parse.hpp"
#include "util.h"
#include <boost/optional.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>

using boost::unit_test::framework::master_test_suite;
namespace x3 = boost::spirit::x3;

// using namespace parser;
using namespace std;
using namespace fol;
using namespace ast;

BOOST_AUTO_TEST_CASE(test_unification) {

    /* --------- List of Test cases for unification -----------
    Variables: v1, v2
    Constants: C2, C3
    Predicates: T(), F1(), E1() 

    1. T(v1) and T(C2)
    2. T(v1, C3) and T(C2, C3)
    3. T(v1, v2) and T(C2, C3)
    4. T(C2, C3) and T(v1, C3)
    5. T(F1(v1)) and T(F1(C2))
    6. T(v1) and T(F1(C2)) -------> Here is a reason to make the sub_list a string -> term mapping since the arguements are lost here.
    7. T(E1(F1(v1)), C3) and T(E1(F1(C2)), v2)
    */

    // BOOST_TEST(true);
    // setup some definitions
    Literal<Term> L1, L2, Parsed_L;
    Term T1, T2, T3, T4, T5, T6, T7, T8;
    Constant C1, C2, C3;
    Variable v1, v2;
    Function F1, F2, F3, F4;
    Predicate P1, P2;
    sub_list test;
    sub_list answer;

    // sample predicates for testing unification

    // T(V1) unified with T(C2)
    // first literal declaration, T(v1)
    v1.name = "v1";
    T1 = v1;
    P1 = "P1";
    L1.predicate = P1;
    L1.args.push_back(T1);
    // second literal declaration, T(C2)
    C2.name = "C2";
    T2 = C2;
    P2 = "P2";
    L2.predicate = P2;
    L2.args.push_back(T2);
    // correct answer declaration, v1->C2
    answer["v1"] = C2;
    // run test for single argument constant unification
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Constant>(test["v1"]).name, get<Constant>(answer["v1"]).name);

    // lets now up the number of arguments, first an extra constant that is already unified
    C3.name = "C3";
    T3 = C3;
    L1.args.push_back(T3);
    L2.args.push_back(T3);
    // clear previous substitution list, answer is the same, no need to clear it 
    test.clear();
    // test unification of T(v1, C3) and T(C2, C3), v1->C2
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Constant>(test["v1"]).name, get<Constant>(answer["v1"]).name);

    // lets now setup for a 2 variable substition 
    v2.name = "v2";
    T4 = v2;
    L1.args.clear();
    L1.args.push_back(T1);
    L1.args.push_back(T4);
    test.clear();
    answer["v2"] = C3;
    // testing unifictation of T(v1, v2) and T(C2, C3)
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Constant>(test["v1"]).name, get<Constant>(answer["v1"]).name);
    BOOST_CHECK_EQUAL(get<Constant>(test["v2"]).name, get<Constant>(answer["v2"]).name);

    // Next let's test if there is a variable in the other literals if the substitution works 

    L1.args.clear();
    L1.args.push_back(T2);
    L1.args.push_back(T3);
    L2.args.clear();
    L2.args.push_back(T1);
    L2.args.push_back(T3);
    test.clear();

    // testing unificatin of T(C2, C3) and T(v1, C3)
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Constant>(test["v1"]).name, get<Constant>(answer["v1"]).name);


    // Next let's test a function for nested predicates in the literal 
    F1.name = "F1";
    F1.args.push_back(T1);
    F2.name = "F1";
    F2.args.push_back(T2);
    T5 = F1;
    T6 = F2;

    L1.args.clear();
    L1.args.push_back(T5);
    L2.args.clear();
    L2.args.push_back(T6);

    test.clear();
    // test of T(F1(v1)) and T(F1(C2)) , so v1->C2
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Constant>(test["v1"]).name, get<Constant>(answer["v1"]).name);

    // add a test case where the variable is equal to a predicate
    L1.args.clear();
    L1.args.push_back(T1);
    test.clear();
    answer.clear();
    answer["v1"] = F1;

    // test of T(v1) and T(F1(C2)), so v1->F1(C2)
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Function>(test["v1"]).name, get<Function>(answer["v1"]).name);

    // last test is a 2 predcicate deep literal with multiple arguments and multiple variables

    F3.name = "E1";
    F3.args.push_back(T5);
    T7 = F3;
    F4.name = "E1";
    F4.args.push_back(T6);
    T8 = F4;
    // should have a form like this: T( E1(F1(v1)), C3) and T( E1(F1(C2)), v2), this should give v1->C2 and v2->C3 (no need to change answer again)
    // fails the test if the nested predicate is first, implies bug in recursion. 
    L1.args.clear();
    L1.args.push_back(T7);
    L1.args.push_back(T3);
    L2.args.clear();
    L2.args.push_back(T8);
    L2.args.push_back(T4);
    test.clear();
    answer.clear();
    answer["v2"] = C3;
    answer["v1"] = C2;

    // running the test
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(get<Constant>(test["v1"]).name, get<Constant>(answer["v1"]).name);
    BOOST_CHECK_EQUAL(get<Constant>(test["v2"]).name, get<Constant>(answer["v2"]).name);    


    // now to run some tests using the PDDl parser
    auto Test_Parsed_L =
        parse<Literal<Term>>("(predicate constant ?variable)", parser::literal_terms_type());
    BOOST_CHECK_EQUAL(Test_Parsed_L.predicate,
               "predicate");

    // To Do:
    // perhaps add failed cases to check return when failed unification????

}
