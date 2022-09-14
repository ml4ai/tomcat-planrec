#define BOOST_TEST_MODULE TestLoader

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

    auto [plantree,indexes] = cppMCTShop(domain,problem,scorers["delivery_one"],30,-1,0.4,19,0.75,2022);
    auto [root,end] = indexes;
    BOOST_TEST(plantree.nodes[end].plan.size() == 9);
    BOOST_TEST(plantree.nodes[end].state.get_facts("at").contains("(at package_0 city_loc_0)"));
    BOOST_TEST(plantree.nodes[end].state.get_facts("at").contains("(at package_1 city_loc_2)"));

}// end of testing the planner


