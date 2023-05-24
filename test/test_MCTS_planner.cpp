#define BOOST_TEST_MODULE TestMCTSPlanner

#include <boost/test/included/unit_test.hpp>
#include "../domains/score_functions.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include "cpphop/loader.h"
#include "cpphop/cppMCTShop.h"

BOOST_AUTO_TEST_CASE(test_MCTS_planner) {
    auto [domain,problem] = load("../../domains/transport_domain.hddl",
                                 "../../domains/transport_problem.hddl");

    auto results = cppMCTShop(domain,problem,scorers["delivery_one"],30,1,-1,sqrt(2.0),2022);;
    BOOST_TEST(results.t[results.end].plan.size() == 8);
    BOOST_TEST(results.t[results.end].state.get_facts("at").contains("(at package_0 city_loc_0)"));
    BOOST_TEST(results.t[results.end].state.get_facts("at").contains("(at package_1 city_loc_2)"));

}// end of testing the planner


