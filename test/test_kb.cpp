#define BOOST_TEST_MODULE TestKB

#include "kb.h"
#include <boost/test/included/unit_test.hpp>

using boost::unit_test::framework::master_test_suite;
using namespace std;
using namespace ast;
using namespace fol;

BOOST_AUTO_TEST_CASE(test_kb) {
    KnowledgeBase kb;
    kb.add_type("target");
    kb.add_type("capacity_number");
    kb.add_type("location");
    kb.add_type("locatable");
    kb.add_type("package","locatable");
    kb.add_type("vehicle","locatable");

    kb.add_object("package_0","package");
    kb.add_object("package_1","package");
    kb.add_object("capacity_0","capacity_number");
    kb.add_object("capacity_1","capacity_number");
    kb.add_object("city_loc_0","location");
    kb.add_object("city_loc_1","location");
    kb.add_object("city_loc_2","location");
    kb.add_object("truck_0","vehicle");
    kb.add_object("surprise","package");

    kb.add_predicate("road",{{"?arg0","location"},{"?arg1","location"}});
    kb.add_predicate("at",{{"?arg0","locatable"},{"?arg1","location"}});
    kb.add_predicate("in",{{"?arg0","package"},{"?arg1","vehicle"}});
    kb.add_predicate("capacity",{{"?arg0","vehicle"},{"?arg1","capacity_number"}});
    kb.add_predicate("capacity_predecessor",{{"?arg0","capacity_number"},{"?arg1","capacity_number"}});

    kb.initialize();

    BOOST_TEST(kb.tell("(capacity_predecessor capacity_0 capacity_1)"));   

    std::cout <<"Added effect"<< std::endl;
    kb.print_pfacts();
    std::cout << std::endl;
    BOOST_TEST(kb.tell("(capacity_predecessor capacity_0 capacity_1)",true));
    std::cout <<"Deleted effect"<< std::endl;
    kb.print_pfacts();

    BOOST_TEST(kb.tell("(capacity_predecessor capacity_0 capacity_1)"));
    BOOST_TEST(kb.tell("(road city_loc_0 city_loc_1)"));
    BOOST_TEST(kb.tell("(road city_loc_1 city_loc_0)"));
    BOOST_TEST(kb.tell("(road city_loc_1 city_loc_2)"));
    BOOST_TEST(kb.tell("(road city_loc_2 city_loc_1)"));
    BOOST_TEST(kb.tell("(at package_0 city_loc_1)"));
    BOOST_TEST(kb.tell("(at package_1 city_loc_1)"));
    BOOST_TEST(kb.tell("(at truck_0 city_loc_2)"));
    BOOST_TEST(kb.tell("(capacity truck_0 capacity_1)"));

    std::string test_expr1 = "(and (at truck_0 city_loc_2) (at package_0 city_loc_1))";

    BOOST_TEST(kb.ask(test_expr1));

    std::string test_expr2 = "(and (at truck_0 city_loc_2) (or (at package_0 city_loc_1) (at package_0 city_loc_2)))";

    BOOST_TEST(kb.ask(test_expr2));

    std::string test_expr3 = "(and (at truck_0 city_loc_2) (at package_0 city_loc_2))";

    BOOST_TEST(!kb.ask(test_expr3));

    std::string test_expr4 = "(road ?c1 ?c2)";
    auto test = kb.ask(test_expr4,{{"?c1","location"},{"?c2","location"}});
    BOOST_TEST(test.size() == 4);
    for (auto const& b : test) {
      for (auto const& [var,val] : b) {
        std::cout << var << " : " << val << std::endl;
      }
    }
}
