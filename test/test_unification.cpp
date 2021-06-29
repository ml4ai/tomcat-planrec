#define BOOST_TEST_MODULE TestUnification

#include <boost/test/included/unit_test.hpp>

#include "fol/Constant.h"
#include "fol/Variable.h"
#include "unification.h"
#include <iostream>

using namespace std;

BOOST_AUTO_TEST_CASE(test_unification) {
    fol::Constant c{"c"};
    // Test whether an empty substitution returns failure
    std::optional<Substitution> theta_failure = std::nullopt; 
    BOOST_TEST(!(unify(c, c, theta_failure)).has_value());

    // Testing whether a non-empty substitution works
    std::optional<Substitution> theta = Substitution();
    theta.value()["c"] = fol::Constant{"c_subst"};
    auto subst = unify(c, c, theta);

    BOOST_TEST(subst.has_value());
    BOOST_TEST(subst.value()["c"].name == "c_subst");

    // Check unification with variables
    fol::Variable v{"v"};
    auto subst_2 = unify(v, c);
    //BOOST_TEST(subst_2.value()["v"].name == "c");
}
