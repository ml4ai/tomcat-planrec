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

BOOST_AUTO_TEST_CASE(test_kb) {
    KnowledgeBase kb;

    initialize_data_types(kb, "Role", {"medic", "transporter", "engineer"});
    initialize_data_types(kb, "Location", {"room1", "room2", "room3"});
    initialize_predicates(kb, "at", {"Role", "Location"});
    tell(kb, "at medic room1");
    tell(kb, "at transporter room1");
    tell(kb, "at engineer room3");
    auto context = get_context(kb);
    cout << context << endl;
    auto res = ask(kb, "at engineer room2");
    BOOST_TEST(res["assertion"].at(0) == "unsat");
    res = ask(kb, "at engineer room3");
    BOOST_TEST(res["assertion"].at(0) == "sat");
    res = ask(kb, "at engineer ?location");
    BOOST_TEST(res["?location"].at(0) == "room3");
    res = ask(kb, "at ?who room1");
    BOOST_TEST(res["?who"].at(0) == "medic");
    BOOST_TEST(res["?who"].at(1) == "transporter");
    res = ask(kb, "at ?who ?location");
    BOOST_TEST(res["?who"].at(0) == "medic");
    BOOST_TEST(res["?location"].at(0) == "room1");
    BOOST_TEST(res["?who"].at(1) == "engineer");
    BOOST_TEST(res["?location"].at(1) == "room3");
    BOOST_TEST(res["?who"].at(2) == "transporter");
    BOOST_TEST(res["?location"].at(2) == "room1");
}
