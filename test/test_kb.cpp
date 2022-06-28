#define BOOST_TEST_MODULE TestKB

#include "fol/Constant.h"
#include "fol/Variable.h"
#include "kb.h"
#include <boost/test/included/unit_test.hpp>

using boost::unit_test::framework::master_test_suite;
using namespace std;
using namespace ast;
using namespace fol;

BOOST_AUTO_TEST_CASE(test_kb) {
    KnowledgeBase kb;

    initialize_data_type(kb, "Role", {"medic", "transporter", "engineer"});
    initialize_data_type(kb, "Victim", {"v1", "v2", "v3"});
    initialize_data_type(kb, "Location", {"room1", "room2", "room3"});
    initialize_data_type(kb, "Victim_Type", {"a", "b", "c"});
    initialize_predicate(kb, "at", {"Role", "Location"});
    initialize_predicate(kb, "vt", {"Victim", "Victim_Type"});
    tell(kb, "(at medic room1)");
    tell(kb, "(at transporter room1)");
    tell(kb, "(at engineer room1)");
    tell(kb, "(at medic room2)");
    tell(kb, "(at transporter room3)");
    tell(kb, "(at medic room1)");
    tell(kb, "(at transporter room1)");
    tell(kb, "(at engineer room3)");
    tell(kb, "(vt v1 a)");
    tell(kb, "(vt v2 b)");
    tell(kb, "(vt v3 c)");
    tell(kb, "(vt v2 c)");
    tell(kb, "(vt v3 a)");

    auto context = get_smt(kb);
    cout << "SMT string: " << endl;
    cout << context << endl;
    auto res = ask(kb, "(at engineer room2)");
    BOOST_TEST(res["assertion"].at(0) == "unsat");
    res = ask(kb, "(at engineer room3)");
    BOOST_TEST(res["assertion"].at(0) == "sat");
    res = ask(kb, "(and (at medic room1) (at transporter room1))");
    BOOST_TEST(res["assertion"].at(0) == "sat");
    res = ask(kb, "(and (at medic room1) (at transporter room3))");
    BOOST_TEST(res["assertion"].at(0) == "unsat");
    res = ask(kb, "(or (at medic room1) (at transporter room3))");
    BOOST_TEST(res["assertion"].at(0) == "sat");
    res = ask(kb, "(and (at medic room1) (at transporter room1) (vt v1 a))");
    BOOST_TEST(res["assertion"].at(0) == "sat");
    res = ask(kb, "(and (at medic room1) (at transporter room1) (vt v2 a))");
    BOOST_TEST(res["assertion"].at(0) == "unsat");
    res = ask(kb,
              "(or (and (at medic room1) (at transporter room1) (vt v1 a)) "
              "(and (at medic room1) (at transporter room1) (vt v2 a)))");
    BOOST_TEST(res["assertion"].at(0) == "sat");
    res = ask(kb, "(at engineer ?location)");
    BOOST_TEST(res["?location"].at(0) == "room3");
    res = ask(kb, "(vt v2 ?type)");
    BOOST_TEST(res["?type"].at(0) == "c");
    res = ask(kb, "(vt v2 ?type)");
    BOOST_TEST(res["?type"].at(0) != "b");
    res = ask(kb, "(vt ?vic a)");
    BOOST_TEST(res["?vic"].at(0) == "v1");
    BOOST_TEST(res["?vic"].at(1) == "v3");
    res = ask(kb, "(at ?who room1)");
    BOOST_TEST(res["?who"].at(0) == "medic");
    BOOST_TEST(res["?who"].at(1) == "transporter");
    res = ask(kb, "(at ?who ?location)");
    BOOST_TEST(res["?who"].at(0) == "medic");
    BOOST_TEST(res["?location"].at(0) == "room1");
    BOOST_TEST(res["?who"].at(1) == "transporter");
    BOOST_TEST(res["?location"].at(1) == "room1");
    BOOST_TEST(res["?who"].at(2) == "engineer");
    BOOST_TEST(res["?location"].at(2) == "room3");
}
