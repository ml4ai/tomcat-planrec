#define BOOST_TEST_MODULE TestUnification

#include <boost/test/included/unit_test.hpp>

#include "CNF.h"
#include "parsing/parse.hpp"
#include "parsing/domain.hpp"
#include <iostream>

using namespace std;

BOOST_AUTO_TEST_CASE(test_cnf_conversion) {
    auto s = parse<ast::Sentence>("(and (a) (or b c))", sentence());
    auto clauses = boost::apply_visitor(ast::DistributeOrOverAnd(), s);
}
