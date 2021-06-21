#define BOOST_TEST_MODULE TestUnification

#include <boost/test/included/unit_test.hpp>

//#include "unification.h"

using namespace std;

BOOST_AUTO_TEST_CASE(test_unification) {

    BOOST_TEST(true);
    // sample predicates for testing unification
    //typedef boost::variant<client::ast::Entity, client::ast::Variable, Predicate> argument; // only boost::variant allows for recursion
    //typedef vector<argument> v_args;

    //client::ast::Entity John("John");
    //client::ast::Entity Richard("Richard");
    //client::ast::Variable X("X");

    //argument J1=John;
    //argument R1=Richard;
    //argument X1=X;

    //v_args v1 (J1, R1);
    //v_args v2 (J1, X1);

    //KnowledgeBase::Predicate P1("Knows", v1);
    //KnowledgeBase::Predicate P2("Knows", v2);

    //// setting up to run unification 
    //typedef unordered_map<string, string> subs;
    //subs s1;

    //s1 = KnowledgeBase.unification(P1, P2, s1);

    //cout << s1;
}