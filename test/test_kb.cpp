#define BOOST_TEST_MODULE TestKB

#include <boost/test/included/unit_test.hpp>

#include "CNF.h"
#include "Clause.h"
#include "fol/Constant.h"
#include "fol/Literal.h"
#include "fol/Variable.h"
#include "kb.h"
#include "parsing/api.hpp"
#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/parse.hpp"
#include "util.h"

using boost::unit_test::framework::master_test_suite;
using namespace std;
using namespace ast;
using namespace fol;

string test_kb1() {
    KnowledgeBase kb;

    initialize_data_types(
        kb, "Role", {"medic", "transporter", "engineer"});
    initialize_data_types(
        kb, "Location", {"room1", "room2", "room3"});
//    initialize_symbols();
    initialize_predicates(kb, "at", {"Role", "Location"});
    tell(kb, "at medic room1");
    tell(kb, "at transporter room1");
    tell(kb, "at engineer room3");
    auto context = get_context(kb);
    auto res = ask(kb, "at engineer room2");
    if (res.size() == 1 and (res.begin()->first == "assertion")){
        cout << res.begin()->second.at(0);
    }

    cout << "";
}

BOOST_AUTO_TEST_CASE(test_kb) { BOOST_TEST(test_kb1() == "sat"); }
