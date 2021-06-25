#define BOOST_TEST_MODULE TestUnification

#include <boost/test/included/unit_test.hpp>
#include <vector>
#include "unification.h"
#include <iostream>
#include "Variable.h"
#include "Constant.h"
#include "Literal.h"
#include "Term.h"
#include "Function.h"
#include "Visitor.h"
#include "boost/variant.hpp"

using namespace std;

BOOST_AUTO_TEST_CASE(test_unification) {

    // BOOST_TEST(true);
    // setup some definitions
    sub_list test;
    sub_list answer;
    Literal L1, L2, L3, L4;
    Term T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12;
    Constant C1, C2, C3, C4, C5, C6;
    Variable v1, v2, v3, v4, v5, v6;
    Function F1, F2, F3, F4;

    // sample predicates for testing unification

    // T(V1) unified with T(C2)
    // first literal declaration, T(v1)
    v1.name = "v1";
    T1 = v1;
    L1.predicate = "T";
    L1.args.push_back(T1);
    // second literal declaration, T(C2)
    C2.name = "C2";
    T2 = C2;
    L2.predicate = "T";
    L2.args.push_back(T2);
    // correct answer declaration, v1->C2
    answer["v1"] = "C2";
    // run test for single argument constant unification
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(test["v1"], answer["v1"]);

    // lets now up the number of arguments, first an extra constant that is already unified
    C3.name = "C3";
    T3 = C3;
    L1.args.push_back(T3);
    L2.args.push_back(T3);
    // clear previous substitution list, answer is the same, no need to clear it 
    test.clear();
    // test unification of T(v1, C3) and T(C2, C3), v1->C2
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(test["v1"], answer["v1"]);

    // lets now setup for a 2 variable substition 
    v2.name = "v2";
    T4 = v2;
    L1.args.clear();
    L1.args.push_back(T1);
    L1.args.push_back(T4);
    test.clear();
    answer["v2"] = "C3";
    // testing unifictation of T(v1, v2) and T(C2, C3)
    test = unification(L1, L2, test);
    BOOST_CHECK_EQUAL(test["v1"], answer["v1"]);
    BOOST_CHECK_EQUAL(test["v2"], answer["v2"]);

    // Next let's test if there is a variable in both literals if the substitution works 

    // example

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
    BOOST_CHECK_EQUAL(test["v1"], answer["v1"]);

}
