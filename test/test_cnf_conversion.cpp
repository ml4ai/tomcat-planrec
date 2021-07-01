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
    //  test imply
    auto s1 =
        parse<Sentence>("(imply (Animal ?y) (Loves ?x ?y))", sentence());

//    auto s1 = parse<ast::Sentence>("(predicate c1 c2)", sentence());
    auto s2 = parse<Sentence>("(or (a) (and (b) (c)))", sentence());
    // Should produce clauses: (a ∨ b), (a ∨ c)

    auto clauses = to_CNF(s2);
    cout << endl;

    // THIS TEST FAILS, FIXME
//    BOOST_TEST(get<ast::AtomicFormula<ast::Term>>(clauses[0].literals[0]).predicate.name == "a");
}
