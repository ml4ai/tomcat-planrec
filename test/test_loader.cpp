#define BOOST_TEST_MODULE TestLoader

#include <boost/test/included/unit_test.hpp>
#include "cpphop/loader.h"

BOOST_AUTO_TEST_CASE(test_domain_loading) {
    // Test loading of domain definition and its components


    DomainDef storage_domain = loadDomain("../../test/storage_domain_test.hddl");
    BOOST_TEST(storage_domain.head == "domain_htn");
}// end of testing the domain
