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
    auto og1 = transport_domain.methods["deliver"][0].get_orderings();
    BOOST_TEST(og1["task0"][0] == "task1");

    for (auto const &[t1,o] : og1) {
      std::cout << t1 << "->["; 
      for (auto const& t2 : o) {
        std::cout << t2 << " ";
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
    
    BOOST_TEST(transport_problem.initF[7] == "(road city_loc_2 city_loc_0)");

    BOOST_TEST(transport_problem.objects.size() == 9);

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
    Args b = {std::make_pair("v","truck_0"),std::make_pair("l1","city_loc_2"),std::make_pair("l2","city_loc_1")};
    auto no_act = actions.at("drive").apply(kb,b);
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
    auto drive_act = actions.at("drive").apply(kb,b);
    BOOST_TEST(drive_act.first == "(drive truck_0 city_loc_2 city_loc_1)");
    BOOST_TEST(drive_act.second.size() == 1);
    std::cout << std::endl;
    std::cout << "#FACTS AFTER DRIVE#" << std::endl;
    drive_act.second[0].print_facts();
    std::cout << std::endl;
    BOOST_TEST(drive_act.second[0].get_facts("at").contains("(at truck_0 city_loc_1)"));
    BOOST_TEST(!drive_act.second[0].get_facts("at").contains("(at truck_0 city_loc_2)"));

    //test method apply
    TaskGraph tg1; 
    Grounded_Task d;
    d.head = "deliver";
    d.args = {std::make_pair("p","package_0"),std::make_pair("l2","city_loc_2")};
    int i = tg1.add_node(d);
    auto deliver_method = transport_domain.methods["deliver"][0].apply(kb,d.args,tg1,i);
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
    TaskGraph tg2;
    Grounded_Task init_d;
    init_d.head = "__delivery__";
    init_d.args = {};
    int j = tg2.add_node(init_d);
    auto init_method = transport_problem.initM.apply(kb,init_d.args,tg2,j);
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
