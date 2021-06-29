#define BOOST_TEST_MODULE TestKB

#include <boost/test/included/unit_test.hpp>

#include "kb.h"

BOOST_AUTO_TEST_CASE(test_kb) {
    auto c = Constant{"const"};
    auto v = Variable{"var"};
    auto v2 = Variable{"var"};
    // auto f = Function{"func"};
    auto p = Literal{"pred"};
    auto kb = KnowledgeBase();
    tell(kb, p);

    // Smokescreen test
    BOOST_TEST(true);
}
