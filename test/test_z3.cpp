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
    s.add(forall(x,implies(k(x) && g(x), e(x))));
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

BOOST_AUTO_TEST_CASE(test_z3) {
    BOOST_TEST(demorgan() == "sat");
    BOOST_TEST(test_logic_infer1() == "sat");
    BOOST_TEST(test_logic_infer2() == "sat");
}
