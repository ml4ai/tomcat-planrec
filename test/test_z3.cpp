#define BOOST_TEST_MODULE TestZ3

#include <boost/test/included/unit_test.hpp>

#include <boost/variant/get.hpp>
#include <fstream>
#include <iostream>
#include <string>

#include "util.h"
#include <boost/optional.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>

using boost::unit_test::framework::master_test_suite;
namespace x3 = boost::spirit::x3;
using namespace std;
using boost::get;
#include "z3++.h"
using namespace z3;

string demorgan() {
    std::cout << "de-Morgan example\n";

    context c;

    expr x = c.bool_const("x");
    expr y = c.bool_const("y");
    expr conjecture = (!(x && y)) == (!x || !y);

    solver s(c);
    // adding the negation of the conjecture as a constraint.
    s.add(!conjecture);
    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer1() {
    context c;

    expr x = c.bool_const("x");
    expr y = c.bool_const("y");
    expr conjecture1 = implies(x, y);
    expr conjecture2 = x;
    expr conjecture3 = y;
    solver s(c);
    // adding the negation of the conjecture as a constraint.
    s.add(conjecture1);
    s.add(conjecture2);
    s.add(!conjecture3);

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer2() {
    std::cout << "quantifier example\n";
    context c;

    expr x = c.bool_const("x");
    expr John = c.bool_const("John");
    z3::sort I = c.bool_sort();
    func_decl k = z3::function("King", I, I);
    func_decl g = z3::function("Greedy", I, I);
    func_decl e = z3::function("Evil", I, I);

    solver s(c);

    // making sure model based quantifier instantiation is enabled.
    params p(c);
    p.set("mbqi", true);
    s.set(p);
    s.add(forall(x, implies(k(x) && g(x), e(x))));
    s.add(k(John));
    s.add(g(John));
    expr conjecture = e(John);
    s.add(!conjecture);

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer3() {
    std::cout << "predicates example\n";
    context c;

    expr role = c.bool_const("role");
    expr location = c.bool_const("location");
    expr medic = c.bool_const("medic");
    expr loc1 = c.bool_const("room1");
    expr loc2 = c.bool_const("room2");

    z3::sort I = c.bool_sort();
    func_decl at = z3::function("at", I, I, I);

    solver s(c);
    s.add(at(role, location));
    s.add(at(medic, loc1));
    expr conjecture = at(medic, loc1);
    s.add(!conjecture);

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer4() {
    std::cout << "parse string\n";
    z3::context c;
    z3::solver s(c);
    s.from_string("(declare-const x Int)(assert (> x 10))");

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer5() {
    std::cout << "test logic\n";
    z3::context c;
    z3::solver s(c);
    s.from_string("(declare-fun medic () Bool)\n"
                  " (declare-fun room1 () Bool)\n"
                  " (declare-fun room2 () Bool)\n"
                  " (declare-fun at (Bool Bool) Bool)\n"
                  " (assert (at medic room1))\n"
                  " (assert (not (at medic room1)))");

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer6() {
    std::cout << "test logic\n";
    z3::context c;
    z3::solver s(c);
    s.from_string(
        "(declare-fun x () Bool)\n"
        " (declare-fun y () Bool)\n"
        " (declare-fun John () Bool)\n"
        " (declare-fun Anil () Bool)\n"
        " (declare-fun Harry () Bool)\n"
        " (declare-fun Apple () Bool)\n"
        " (declare-fun Peanuts () Bool)\n"
        " (declare-fun vegetables () Bool)\n"
        " (declare-fun food (Bool) Bool)\n"
        " (declare-fun likes (Bool Bool) Bool)\n"
        " (declare-fun eats (Bool Bool) Bool)\n"
        " (declare-fun killed (Bool) Bool)\n"
        " (declare-fun alive (Bool) Bool)\n"
        " (assert (forall ((x Bool)) (=> (food x) (likes John x))))\n"
        " (assert (and (food Apple) (food vegetables)))\n"
        " (assert (forall ((x Bool)) (forall ((y Bool)) (=> (and (eats x y) "
        "(not (killed x))) (food y)))))\n"
        " (assert (and (eats Anil Peanuts) (alive Anil)))\n"
        " (assert (forall ((x Bool)) (=> (eats Anil x) (eats Harry x))))\n"
        " (assert (forall ((x Bool)) (=> (not (killed x)) (alive x))))\n"
        " (assert (forall ((x Bool)) (=> (alive x) (not (killed x)))))\n"
        " (assert (not (likes John Peanuts)))");

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

string test_logic_infer7() {
    std::cout << "test logic\n";
    z3::context c;
    z3::solver s(c);
    s.from_string(
        "(declare-fun x () Bool)\n"
        " (declare-fun y () Bool)\n"
        " (declare-fun z () Bool)\n"
        " (declare-fun Jack () Bool)\n"
        " (declare-fun Tuna () Bool)\n"
        " (declare-fun Curiosity () Bool)\n"
        " (declare-fun Animal (Bool) Bool)\n"
        " (declare-fun Loves (Bool Bool) Bool)\n"
        " (declare-fun Kills (Bool Bool) Bool)\n"
        " (declare-fun Cat (Bool) Bool)\n"
        " (assert (forall ((x Bool)) (=> (forall ((y Bool)) (=> (Animal y)\n"
        " (Loves x y))) (exists ((y Bool)) (Loves y x)))))\n"
        " (assert (forall ((x Bool)) (=> (exists ((z Bool)) (and (Animal z)\n"
        " (Kills x z))) (forall ((y Bool)) (not (Loves y x))))))\n"
        " (assert (forall ((x Bool)) (=> (Animal x) (Loves Jack x))))\n"
        " (assert (or (Kills Jack Tuna) (Kills Curiosity Tuna)))\n"
        " (assert (Cat Tuna))\n"
        " (assert (forall ((x Bool)) (=> (Cat x) (Animal x))))\n"
        " (assert (not (Kills Curiosity Tuna)))");

    switch (s.check()) {
    case unsat:
        return "sat";
    case sat:
        return "unsat";
    case unknown:
        return "unknown";
    }
}

BOOST_AUTO_TEST_CASE(test_z3) {
    BOOST_TEST(demorgan() == "sat");
    BOOST_TEST(test_logic_infer1() == "sat");
    BOOST_TEST(test_logic_infer2() == "sat");
    BOOST_TEST(test_logic_infer3() == "sat");
    BOOST_TEST(test_logic_infer4() == "unsat");
    BOOST_TEST(test_logic_infer5() == "sat");
    BOOST_TEST(test_logic_infer6() == "sat");
    BOOST_TEST(test_logic_infer7() == "sat");
}
