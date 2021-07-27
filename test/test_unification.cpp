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

    TODO - implement some/all of the tests below.

    1. F1(v1) and F1(C2)
    2. T(v1) and F1(C2) -------> Here is a reason to make the sub_list a
    string -> term mapping since the arguements are lost here.
    3. T(E1(F1(v1)), C3) and T(E1(F1(C2)), v2)
    4. Here is a fail test case where unification is not possible:
        9.1 Different number of argument of literal
        9.2 No variable is given
        9.3 different nested predicates
    */

}
