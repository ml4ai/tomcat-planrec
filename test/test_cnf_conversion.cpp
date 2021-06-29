#define BOOST_TEST_MODULE TestUnification

#include <boost/test/included/unit_test.hpp>

#include "CNF.h"
#include "parsing/parse.hpp"
#include "parsing/domain.hpp"
#include <iostream>

using namespace std;
using boost::get;

BOOST_AUTO_TEST_CASE(test_cnf_conversion) {
    auto s1 = parse<ast::Sentence>("(predicate c1 c2)", sentence());
    BOOST_TEST(to_CNF(s1)[0].predicate.name == "predicate");
    auto s = parse<ast::Sentence>("(or (a) (and b c))", sentence());
    // Should produce clauses: (a ∨ b), (a ∨ c)
    auto clauses = to_CNF(s);
    //BOOST_TEST(get<ast::AtomicFormula<ast::Term>>(clauses[0].literals[0]).predicate.name == "a");
}
