#define BOOST_TEST_MODULE TestLoader

#include <boost/test/included/unit_test.hpp>
#include "cpphop/loader.h"

BOOST_AUTO_TEST_CASE(test_domain_loading) {
    // Test loading of domain definition and its components


    DomainDef storage_domain = loadDomain("../../test/storage_domain_test.hddl");
    BOOST_TEST(storage_domain.head == "domain_htn");

    BOOST_TEST(storage_domain.types.size() == 2);
    BOOST_TEST(storage_domain.types["object"].size() == 4);
    BOOST_TEST(storage_domain.types["object"][0] == "capacity_number");

    BOOST_TEST(storage_domain.predicates.size() == 5);
    BOOST_TEST(storage_domain.predicates[2].first == "in");
    BOOST_TEST(storage_domain.predicates[2].second[0].first == "arg0");
    BOOST_TEST(storage_domain.predicates[2].second[1].first == "arg1");
    BOOST_TEST(storage_domain.predicates[2].second[1].second == "vehicle");

    // Test parsing of abstract tasks
    BOOST_TEST(storage_domain.tasks[0].first == "deliver");
    auto taskpara1 = storage_domain.tasks[0].second;
    BOOST_TEST(taskpara1[0].second == "package");

    // Test methods and their components (totally-ordered):
    // Test methods name:
    BOOST_TEST(storage_domain.methods["deliver"][0].get_head() == "m_deliver_ordering_0");

    // Test Methods Parameters:
    BOOST_TEST(storage_domain.methods["deliver"][0].get_parameters()[2].second == "package");

    // Test method's task to be broken down. In the abstract task, 'task' is
    // defined similar to an action. Here, it is defined as <Literal<Term>>
    auto methodtask = storage_domain.methods["deliver"][0].get_task();
    BOOST_TEST(methodtask.first == "deliver");
    BOOST_TEST(methodtask.second[0].first == "p");
    // Test parsing method's precondition:
    auto methodprec_f = storage_domain.methods["deliver"][0].get_preconditions();
    BOOST_TEST(methodprec_f == "__NONE__");

    auto methodprec_complex = storage_domain.methods["test_task"][0].get_preconditions();
    std::cout <<"#TESTING COMPLEX PRECONDITIONS#" << std::endl;
    std::cout << methodprec_complex << std::endl;
    std::cout << std::endl;

    // Test Parsing Method's SubTasks:
    BOOST_TEST(storage_domain.methods["deliver"][0].get_subtasks()[2].first == "get_to");
    BOOST_TEST(storage_domain.methods["deliver"][0].get_subtasks()[2].second[1].first == "l2");

    // Test parsing of domain actions and their components:
    // Test parsing action names
    auto actname1 = storage_domain.actions.at("drive").get_head();
    BOOST_TEST(actname1 == "drive");

    // Test parsing action parameters
    auto actpara1 = storage_domain.actions.at("drive").get_parameters();
    BOOST_TEST(actpara1[0].second == "vehicle");
    BOOST_TEST(actpara1[2].second == "location");
    BOOST_TEST(actpara1[0].first == "v");
    BOOST_TEST(actpara1[2].first == "l2");

    // Test parsing action precondition
    auto actprec = storage_domain.actions.at("drive").get_preconditions();
    BOOST_TEST(actprec == "(and (at v l1) (road l1 l2))");

    // Test parsing action effect
    
    auto effects = storage_domain.actions.at("drive").get_effects();
    BOOST_TEST(effects[0].pred.first == "at");
    BOOST_TEST(effects[0].pred.second[0].first == "v");
    BOOST_TEST(effects[0].remove == true);

    std::cout <<"#TESTING COMPLEX EFFECTS#" << std::endl;
    auto effects_complex = storage_domain.actions.at("test_action").get_effects();
    for (auto const& e : effects_complex) {
      std::cout << "condition for " << e.pred.first << ": "<< e.condition << std::endl;
      if (e.remove) {
        std::cout << e.pred.first << " is being removed." << std::endl; 
      }
      else {
        std::cout << e.pred.first << " is being added." << std::endl;
      }
      std::cout << "Forall types for " << e.pred.first << ": " << std::endl;
      for (auto const& [var,types] : e.forall) {
        std::cout << var << " -";
        for (auto const& t : types) {
          std::cout << " " << t;
        }
        std::cout << std::endl;
      }
    }
}// end of testing the domain