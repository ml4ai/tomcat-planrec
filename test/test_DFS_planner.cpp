#define BOOST_TEST_MODULE TestDFSPlanner

#include <boost/test/included/unit_test.hpp>

#include "../apps/planners/domains/simple_travel.h"

BOOST_AUTO_TEST_CASE(test_DFS_planner) {
    auto state1 = TravelState("state1");
    state1.loc["me"] = "home";
    state1.cash["me"] = 20;
    state1.owe["me"] = 0;
    state1.dist["home"]["park"] = 1;
    state1.dist["park"]["home"] = 1;
    auto domain = TravelDomain();

    auto selector = TravelSelector();

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}))}};
    auto plans = cpphopDFS(state1, tasks, domain, selector);
    BOOST_TEST(plans.size() == 2);
    
    std::string plan1task1 = task2string(plans[0].second[0]);
    BOOST_TEST(plan1task1 == "(walk,park,home,me,)");

    std::string plan2task1 = task2string(plans[1].second[0]);
    BOOST_TEST(plan2task1 == "(call_taxi,home,me,)");

    std::string plan2task2 = task2string(plans[1].second[1]);
    BOOST_TEST(plan2task2 == "(ride_taxi,park,home,me,)");

    std::string plan2task3 = task2string(plans[1].second[2]);
    BOOST_TEST(plan2task3 == "(pay_driver,me,)");
}
