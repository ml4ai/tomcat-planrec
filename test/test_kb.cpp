#define BOOST_TEST_MODULE TestKB

#include "kb.h"
#include "typedefs.h"
#include <boost/test/included/unit_test.hpp>

using boost::unit_test::framework::master_test_suite;
using namespace std;
using namespace ast;
using namespace fol;

BOOST_AUTO_TEST_CASE(test_kb) {
    TypeTree typetree;
    std::string root = "__Object__";
    typetree.add_root(root);
    typetree.add_child("target",root);
    typetree.add_child("capacity_number",root);
    typetree.add_child("location",root);
    typetree.add_child("locatable",root);
    typetree.add_child("package","locatable");
    typetree.add_child("vehicle","locatable");

    Objects objects;
    objects["package_0"] = "package";
    objects["package_1"] = "package";
    objects["capacity_0"] = "capacity_number";
    objects["capacity_1"] = "capacity_number";
    objects["city_loc_0"] = "location";
    objects["city_loc_1"] = "location";
    objects["city_loc_2"] = "location";
    objects["truck_0"] = "vehicle";
    objects["surprise"] = "package";

    Predicates predicates;
    Args a1 = {std::make_pair("?arg0","location"),std::make_pair("?arg1","location")};
    Args a2 = {std::make_pair("?arg0","locatable"),std::make_pair("?arg1","location")};
    Args a3 = {std::make_pair("?arg0","package"),std::make_pair("?arg1","vehicle")};
    Args a4 = {std::make_pair("?arg0","vehicle"),std::make_pair("?arg1","capacity_number")};
    Args a5 = {std::make_pair("?arg0","capacity_number"),std::make_pair("?arg1","capacity_number")};
    predicates.push_back(create_predicate("road", a1));
    predicates.push_back(create_predicate("at", a2));
    predicates.push_back(create_predicate("in", a3));
    predicates.push_back(create_predicate("capacity", a4));
    predicates.push_back(create_predicate("capacity_predecessor", a5));

    KnowledgeBase kb(predicates,objects,typetree);

    BOOST_TEST(kb.tell("(capacity_predecessor capacity_0 capacity_1)",false,false));   

    BOOST_TEST(kb.tell("(capacity_predecessor capacity_0 capacity_1)",true,false));

    BOOST_TEST(kb.tell("(capacity_predecessor capacity_0 capacity_1)",false,false));
    BOOST_TEST(kb.tell("(road city_loc_0 city_loc_1)",false,false));
    BOOST_TEST(kb.tell("(road city_loc_1 city_loc_0)",false,false));
    BOOST_TEST(kb.tell("(road city_loc_1 city_loc_2)",false,false));
    BOOST_TEST(kb.tell("(road city_loc_2 city_loc_1)",false,false));
    BOOST_TEST(kb.tell("(at package_0 city_loc_1)",false,false));
    BOOST_TEST(kb.tell("(at package_1 city_loc_1)",false,false));
    BOOST_TEST(kb.tell("(at truck_0 city_loc_2)",false,false));
    BOOST_TEST(kb.tell("(capacity truck_0 capacity_1)",false,false));

    kb.update_state();

    kb.print_smt_state();

    std::string test_expr1 = "(and (at truck_0 city_loc_2) (at package_0 city_loc_1))";

    BOOST_TEST(kb.ask(test_expr1));

    std::string test_expr2 = "(and (at truck_0 city_loc_2) (or (at package_0 city_loc_1) (at package_0 city_loc_2)))";

    BOOST_TEST(kb.ask(test_expr2));

    std::string test_expr3 = "(and (at truck_0 city_loc_2) (at package_0 city_loc_2))";

    BOOST_TEST(!kb.ask(test_expr3));

    std::string test_expr4 = "(road ?c1 ?c2)";
    std::vector<std::pair<std::string,std::string>> args1 = {std::make_pair("?c1","location"),std::make_pair("?c2","location")};
    auto bindings1 = kb.ask(test_expr4,args1);
    BOOST_TEST(bindings1.size() == 4);
    for (auto const& b : bindings1) {
      for (auto const& vals : b) {
        std::cout << vals.first << " : " << vals.second << std::endl;
      }
    }

    std::vector<std::pair<std::string,std::string>> args2 = {std::make_pair("?p","package"),std::make_pair("?v","vehicle")};
    std::string test_expr5 = "(in ?p ?v)";
    auto bindings2 = kb.ask(test_expr5, args2);
    BOOST_TEST(bindings2.size() == 0);
    //for (auto const& b : test) {
    //  for (auto const& [var,val] : b) {
    //    std::cout << var << " : " << val << std::endl;
    //  }
    //}

}

//Commented this test out for github workflow, you can uncommented it to test
//if the redis pipeline works for the kb.
//BOOST_AUTO_TEST_CASE(test_temporal_facts) {
//    TypeTree typetree;
//    std::string root = "__Object__";
//    typetree.add_root(root);
//    typetree.add_child("locatable",root);
//    typetree.add_child("package","locatable");
//
//    Objects objects;
//    objects["package_0"] = "package";
//
//    Predicates predicates;
//    Args a = {std::make_pair("?arg0", "package")};
//    predicates.push_back(create_predicate("see_package",a));
//
//    KnowledgeBase kb(predicates,objects,typetree);
//
//    kb.update_state();
//
//    kb.print_smt_state();
//
//    kb.update_temporal_facts("tcp://127.0.0.1:6379");
//
//    kb.update_state(0);
//
//    kb.print_smt_state();
//
//    std::string test_expr = "(see_package package_0)";
//
//    if (kb.temporal_facts_is_empty()) {
//      BOOST_TEST(!kb.ask(test_expr)); 
//    }
//    else {
//      // In redis-cli with redis-server running do XADD fov 0-* see_package "(see_package package_0)"
//      BOOST_TEST(kb.ask(test_expr));
//    }
//}
