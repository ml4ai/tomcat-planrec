#define BOOST_TEST_MODULE TestLoader

#include <boost/test/included/unit_test.hpp>
#include "cpphop/loader.h"

BOOST_AUTO_TEST_CASE(test_domain_loading) {
    // Test loading of domain definition and its components
    auto [transport_domain,transport_problem] = load("../../domains/transport_domain.hddl",
                                            "../../domains/transport_problem.hddl");

    BOOST_TEST(transport_domain.head == "domain_htn");

    BOOST_TEST(transport_domain.typetree.types.size() == 8);
    for (auto const& [id, t] : transport_domain.typetree.types) {
      std::cout << t.type << "->["; 
      for (auto const& c : t.children) {
        std::cout << transport_domain.typetree.types[c].type << " "; 
      }
      std::cout << "]" << std::endl;
    }

    BOOST_TEST(transport_domain.predicates.size() == 5);
    BOOST_TEST(transport_domain.predicates[2].first == "in");
    BOOST_TEST(transport_domain.predicates[2].second[0].first == "arg0");
    BOOST_TEST(transport_domain.predicates[2].second[1].first == "arg1");
    BOOST_TEST(transport_domain.predicates[2].second[1].second == "vehicle");

    // Test methods and their components (totally-ordered):
    // Test methods name:
    BOOST_TEST(transport_domain.methods["deliver"][0].get_head() == "m_deliver_ordering_0");

    // Test Methods Parameters:
    BOOST_TEST(transport_domain.methods["deliver"][0].get_parameters()[2].second == "package");

    // Test method's task to be broken down. In the abstract task, 'task' is
    // defined similar to an action. Here, it is defined as <Literal<Term>>
    auto methodtask = transport_domain.methods["deliver"][0].get_task();
    BOOST_TEST(methodtask.first == "deliver");
    BOOST_TEST(methodtask.second[0].first == "p");
    // Test parsing method's precondition:
    auto methodprec_f = transport_domain.methods["deliver"][0].get_preconditions();
    BOOST_TEST(methodprec_f == "(and (at p l1))");

    // Test Parsing Method's SubTasks (in reverse order for planner):
    BOOST_TEST(transport_domain.methods["deliver"][0].get_subtasks()["task1"].first == "load");
    BOOST_TEST(transport_domain.methods["deliver"][0].get_subtasks()["task1"].second[1].first == "l1");

    // Ordering constraints
    auto og1 = transport_domain.methods["deliver"][0].get_id_orderings();
    int t0 = og1.find_Task_ID("task0");
    int t1 = og1.find_Task_ID("task1");
    BOOST_TEST((t0 != -1 && t1 != -1));

    BOOST_TEST(og1[t0].outgoing.contains(t1));
    BOOST_TEST(og1[t1].incoming.contains(t0));
    for (auto const &[id,o] : og1.Task_IDs) {
      std::cout << o.id << "->["; 
      for (auto const& out : o.outgoing) {
        std::cout << og1[out].id << " ";
      }
      std::cout << "]" << std::endl;
    }
    // Test parsing of domain actions and their components:
    // Test parsing action names
    auto actname1 = transport_domain.actions.at("drive").get_head();
    BOOST_TEST(actname1 == "drive");

    // Test parsing action parameters
    auto actpara1 = transport_domain.actions.at("drive").get_parameters();
    BOOST_TEST(actpara1[0].second == "vehicle");
    BOOST_TEST(actpara1[2].second == "location");
    BOOST_TEST(actpara1[0].first == "v");
    BOOST_TEST(actpara1[2].first == "l2");

    // Test parsing action precondition
    auto actprec = transport_domain.actions.at("drive").get_preconditions();
    BOOST_TEST(actprec == "(and (at v l1) (road l1 l2))");

    // Test parsing action effect
    
    auto effects = transport_domain.actions.at("drive").get_effects();
    BOOST_TEST(effects[0].pred.first == "at");
    BOOST_TEST(effects[0].pred.second[0].first == "v");
    BOOST_TEST(effects[0].remove == true);

    auto no_effects = transport_domain.actions.at("noop").get_effects();
    BOOST_TEST(no_effects.size() == 0);

}// end of testing the domain

BOOST_AUTO_TEST_CASE(test_problem_loading) {
    // Test loading of problem definition and its components
    auto [transport_domain,transport_problem] = load("../../domains/transport_domain.hddl",
                                            "../../domains/transport_problem.hddl");

    BOOST_TEST(transport_problem.head == "__delivery__");
    BOOST_TEST(transport_problem.domain_name == "domain_htn");
    
    BOOST_TEST(transport_problem.initF[7] == "(at truck_0 city_loc_2)");

    BOOST_TEST(transport_problem.objects.size() == 8);

    BOOST_TEST(transport_problem.objects["package_0"] == "package");

    BOOST_TEST(transport_problem.initM.get_head() == ":htn");

    BOOST_TEST(transport_problem.initM.get_subtasks()["task1"].first == "deliver");
    BOOST_TEST(transport_problem.initM.get_subtasks()["task1"].second[0].first == "package_1");
}

BOOST_AUTO_TEST_CASE(test_apply) {
    // Test loading of problem definition and its components
    auto [transport_domain,transport_problem] = load("../../domains/transport_domain.hddl",
                                            "../../domains/transport_problem.hddl");
    KnowledgeBase kb(transport_domain.predicates,transport_problem.objects,transport_domain.typetree);
    std::cout << std::endl;
    std::cout << "#ONLY OBJECT FACTS#" << std::endl; 
    kb.print_facts();
    BOOST_TEST(kb.get_facts("vehicle").contains("(vehicle truck_0)"));
    auto actions = transport_domain.actions;
    //test unmet preconditions
    auto no_act = actions.at("drive").apply(kb,
        {std::make_pair("v","truck_0"),std::make_pair("l1","city_loc_2"),std::make_pair("l2","city_loc_1")});
    BOOST_TEST(no_act.second.empty());

    for (auto const& f : transport_problem.initF) {
      kb.tell(f,false,false);
    }
    kb.update_state();
    std::cout << std::endl;
    std::cout << "#INITIAL FACTS#" << std::endl;
    kb.print_facts();
    BOOST_TEST(kb.get_facts("road").contains("(road city_loc_2 city_loc_1)"));

    //test action apply
    auto drive_act = actions.at("drive").apply(kb,
        {std::make_pair("v","truck_0"),std::make_pair("l1","city_loc_2"),std::make_pair("l2","city_loc_1")});
    BOOST_TEST(drive_act.first == "(drive truck_0 city_loc_2 city_loc_1)");
    BOOST_TEST(drive_act.second.size() == 1);
    std::cout << std::endl;
    std::cout << "#FACTS AFTER DRIVE#" << std::endl;
    drive_act.second[0].print_facts();
    std::cout << std::endl;
    BOOST_TEST(drive_act.second[0].get_facts("at").contains("(at truck_0 city_loc_1)"));
    BOOST_TEST(!drive_act.second[0].get_facts("at").contains("(at truck_0 city_loc_2)"));

    //test method apply
    auto deliver_method = transport_domain.methods["deliver"][0].apply(kb,
        {std::make_pair("p","package_0"),std::make_pair("l2","city_loc_2")});
    BOOST_TEST(deliver_method.first == "(deliver package_0 city_loc_2)");
    std::cout <<"#GROUNDED TASKS FOR DELIVER#" << std::endl; 
    for (auto &gts : deliver_method.second) {
      for (auto const &[id,gt] : gts.GTs) {
        std::cout << gt.to_string() << "->["; 
        for (auto &out : gt.outgoing) {
          std::cout << gts[out].to_string() << " ";
        }
        std::cout << "]" << std::endl;
      }
      std::cout << std::endl;
    }

    auto init_method = transport_problem.initM.apply(kb,{});
    std::cout <<"#GROUNDED TASKS FOR DELIVER#" << std::endl; 
    for (auto &gts : init_method.second) {
      for (auto const &[id,gt] : gts.GTs) {
        std::cout << gt.to_string() << "->["; 
        for (auto &out : gt.outgoing) {
          std::cout << gts[out].to_string() << " ";
        }
        std::cout << "]" << std::endl;
      }
      std::cout << std::endl;
    }

}
