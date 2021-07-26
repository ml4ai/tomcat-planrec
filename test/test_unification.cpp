#define BOOST_TEST_MODULE TestUnification

#include "boost/test/included/unit_test.hpp"
#include "boost/variant.hpp"
#include "fol/Constant.h"
#include "fol/Function.h"
#include "fol/Literal.h"
#include "fol/Term.h"
#include "fol/Variable.h"
#include "unification.h"
#include <iostream>
#include <unordered_map>
#include <vector>

#include "boost/optional.hpp"
#include "boost/spirit/home/x3/support/ast/variant.hpp"
#include "parsing/api.hpp"
#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/parse.hpp"
#include "util.h"

using boost::unit_test::framework::master_test_suite;
namespace x3 = boost::spirit::x3;

// using namespace parser;
using namespace std;
using namespace fol;
using namespace ast;
using boost::get;

BOOST_AUTO_TEST_CASE(test_unification) {
    // Constants
    auto c1 = Constant{"c1"};
    auto c2 = Constant{"c2"};

    // Variables
    auto v1 = Variable{"v1"};
    auto v2 = Variable{"v2"};

    // Test unifying constants
    auto subst = unify(c1, c2);
    BOOST_TEST(!subst);

    // Test unifying a variable and a constant
    subst = unify(v1, c2);
    BOOST_TEST(get<Constant>(subst.value().at(v1)) == c2);

    // Test unifying variables
    subst = unify(v1, v2);
    BOOST_TEST(get<Variable>(subst.value().at(v1)) == v2);

    auto lit1 = parse<Literal<Term>>("(Knows John ?x)");

    auto lit2 = parse<Literal<Term>>("(Knows John Jane)");
    subst = unify(lit1, lit2);
    BOOST_TEST(check_substitution_contains(subst, Variable{"x"}, Constant{"Jane"}));

    auto lit3 = parse<Literal<Term>>("(Knows ?y Bill)");
    subst = unify(lit1, lit3);
    BOOST_TEST(check_substitution_contains(subst, Variable{"x"}, Constant{"Bill"}));
    BOOST_TEST(check_substitution_contains(subst, Variable{"y"}, Constant{"John"}));

    auto lit4 = parse<Literal<Term>>("(Knows ?x Elizabeth)");
    subst = unify(lit1, lit4);
    BOOST_TEST(!subst);

    // Test occur check
    BOOST_TEST(occur_check(v1, v1));
    BOOST_TEST(!occur_check(v1, v2));
    BOOST_TEST(occur_check(Variable{"x"}, lit4));

    auto mother = Function{"Mother", {Variable{"y"}}};

    subst = unify(lit1, Literal<Term>{"Knows", {Variable{"y"}, mother}});
    BOOST_TEST(check_substitution_contains(subst, Variable{"x"}, mother));
    BOOST_TEST(check_substitution_contains(subst, Variable{"y"}, Constant{"John"}));



    /* --------- List of Test cases for unification -----------

    5. T(F1(v1)) and T(F1(C2))
    6. T(v1) and T(F1(C2)) -------> Here is a reason to make the sub_list a
    string -> term mapping since the arguements are lost here.
    7. T(E1(F1(v1)), C3) and T(E1(F1(C2)), v2)
    8. Parsing unfication tests predicate(con_1, var_1) and predicate(con_1,
    con_2)
    9. Here is a fail test case where unification is not possible:
        9.1 Different number of argument of literal
        9.2 No variable is given
        9.3 different nested predicates
    */

    // T(V1) unified with T(C2)
    // first literal declaration, T(v1)
    // v1.name = "v1";
    // T1 = v1;
    // P1 = "P1";
    // L1.predicate = P1;
    // L1.args.push_back(T1);
    //// second literal declaration, T(C2)
    // C2.name = "C2";
    // T2 = C2;
    // P2 = "P2";
    // L2.predicate = P2;
    // L2.args.push_back(T2);
    //// correct answer declaration, v1->C2
    // get<sub_list_type>(answer)["v1"] = C2;
    //// run test for single argument constant unification
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v1"]).name);

    //// lets now up the number of arguments, first an extra constant that is
    /// already unified
    // C3.name = "C3";
    // T3 = C3;
    // L1.args.push_back(T3);
    // L2.args.push_back(T3);
    //// clear previous substitution list, answer is the same, no need to clear
    /// it
    // get<sub_list_type>(test).clear();
    //// test unification of T(v1, C3) and T(C2, C3), v1->C2
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v1"]).name);

    //// lets now setup for a 2 variable substition
    // v2.name = "v2";
    // T4 = v2;
    // L1.args.clear();
    // L1.args.push_back(T1);
    // L1.args.push_back(T4);
    // get<sub_list_type>(test).clear();
    // get<sub_list_type>(answer)["v2"] = C3;
    //// testing unifictation of T(v1, v2) and T(C2, C3)
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v1"]).name);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v2"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v2"]).name);

    //// Next let's test if there is a variable in the other literals if the
    /// substitution works

    // L1.args.clear();
    // L1.args.push_back(T2);
    // L1.args.push_back(T3);
    // L2.args.clear();
    // L2.args.push_back(T1);
    // L2.args.push_back(T3);
    // get<sub_list_type>(test).clear();

    //// testing unificatin of T(C2, C3) and T(v1, C3)
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v1"]).name);

    //// Next let's test a function for nested predicates in the literal
    // F1.name = "F1";
    // F1.args.push_back(T1);
    // F2.name = "F1";
    // F2.args.push_back(T2);
    // T5 = F1;
    // T6 = F2;

    // L1.args.clear();
    // L1.args.push_back(T5);
    // L2.args.clear();
    // L2.args.push_back(T6);

    // get<sub_list_type>(test).clear();
    //// test of T(F1(v1)) and T(F1(C2)) , so v1->C2
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v1"]).name);

    //// add a test case where the variable is equal to a predicate
    // L1.args.clear();
    // L1.args.push_back(T1);
    // get<sub_list_type>(test).clear();
    // get<sub_list_type>(answer).clear();
    // get<sub_list_type>(answer)["v1"] = F1;

    //// test of T(v1) and T(F1(C2)), so v1->F1(C2)
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Function>(get<sub_list_type>(test)["v1"]).name ==
    // get<Function>(get<sub_list_type>(answer)["v1"]).name);

    //// last test is a 2 predcicate deep literal with multiple arguments and
    /// multiple variables

    // F3.name = "E1";
    // F3.args.push_back(T5);
    // T7 = F3;
    // F4.name = "E1";
    // F4.args.push_back(T6);
    // T8 = F4;
    //// should have a form like this: T( E1(F1(v1)), C3) and T( E1(F1(C2)),
    /// v2), this should give v1->C2 and v2->C3 (no need to change answer again)
    //// fails the test if the nested predicate is first, implies bug in
    /// recursion.
    // L1.args.clear();
    // L1.args.push_back(T7);
    // L1.args.push_back(T3);
    // L2.args.clear();
    // L2.args.push_back(T8);
    // L2.args.push_back(T4);
    // get<sub_list_type>(test).clear();
    // get<sub_list_type>(answer).clear();
    // get<sub_list_type>(answer)["v2"] = C3;
    // get<sub_list_type>(answer)["v1"] = C2;

    //// running the test
    // test = unify(L1, L2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v1"]).name);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["v2"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["v2"]).name);

    //// now to run some tests using the PDDl parser to show how it works and
    /// then test it out on our algorithm
    // auto s1 = parse<Sentence>("(predicate con_1 ?var_1)", sentence());
    // Literal<Term> lit1 = get<Literal<Term>>(s1);
    // BOOST_TEST(lit1.predicate == "predicate");
    // Constant con_1 = get<Constant>(lit1.args[0]);
    // BOOST_TEST(con_1.name == "con_1");
    // Variable var_1 = get<Variable>(lit1.args[1]);
    // BOOST_TEST(var_1.name == "var_1");

    //// now to run a test with 2 literals parsed from sentences, unifiying them
    // auto s2 = parse<Sentence>("(predicate con_1 con_2)", sentence());
    // Literal<Term> lit2 = get<Literal<Term>>(s2);
    // Constant con_2 = get<Constant>(lit2.args[1]);
    // get<sub_list_type>(test).clear();
    // get<sub_list_type>(answer).clear();
    // get<sub_list_type>(answer)["var_1"] = con_2;

    // test = unify(lit1, lit2, test);
    // BOOST_TEST(get<Constant>(get<sub_list_type>(test)["var_1"]).name ==
    // get<Constant>(get<sub_list_type>(answer)["var_1"]).name);

    //// now for some FAIL checking too with parsed sentences
    // auto s3 = parse<Sentence>("(predicate con_2 ?var_3)", sentence());
    // Literal<Term> lit3 = get<Literal<Term>>(s3);
    // get<sub_list_type>(test).clear();
    // get<sub_list_type>(answer).clear();
    // sub_list answer_s, test1;
    // answer_s = "Error: Constants or Predicates do not match. Unification is
    // not possible.";

    // test1 = unify(lit2, lit3, test1);
    // BOOST_TEST(get<string>(test1) == get<string>(answer_s));

    //// now to test for non atching number of arguments
    // auto s4 = parse<Sentence>("(predicate ?var_2 con_3 con_4)", sentence());
    // Literal<Term> lit4 = get<Literal<Term>>(s4);
    // sub_list answer_s2, test2;
    // answer_s2 = "Error: Predicates have different numbers of arguments.
    // Unification not possible.";

    // test2 = unify(lit1, lit4, test2);
    // BOOST_TEST(get<string>(test2) == get<string>(answer_s2));
}
