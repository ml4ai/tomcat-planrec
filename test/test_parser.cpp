#define BOOST_TEST_MODULE TestParser

#include <boost/test/included/unit_test.hpp>

#include <fstream>
#include <iostream>
#include <string>

#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/config.hpp"
#include "parsing/domain.hpp"
#include "parsing/error_handler.hpp"

using boost::unit_test::framework::master_test_suite;

void print(client::ast::Domain dom) {
    using namespace std;
    cout << "Name: " << dom.name << endl;
    cout << "Requirements: " << endl;
    for (auto x : dom.requirements) {
        cout << '"' << x << '"' << endl;
    }
    cout << endl;
    cout << "Types: " << endl;
    for (auto x : dom.types) {
        cout << x << endl;;
    }
    cout << endl;

    cout << "Actions:" << endl;
    for (auto x : dom.actions) {
        cout << x.name << endl;
        cout << "parameters: " << endl;
        for (auto p : x.parameters) {
            cout << p << endl;
        }
        cout << endl;
    }
    cout << endl;

    cout << "Constants:" << endl;
    for (auto constant : dom.constants) {
        cout << constant;
    }
    cout << endl;
    cout << endl;

    cout << "Predicates:" << endl;
    for (auto x : dom.predicates) {
        cout << x.predicate;
        for (auto variable : x.variables) {
            cout << variable << endl;
        }
    }
    cout << endl;

}
////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////
BOOST_AUTO_TEST_CASE(test_parser) {
    using namespace std;
    typedef string::const_iterator iterator_type;
    using client::domain;


    char const* filename;
    BOOST_TEST_REQUIRE(master_test_suite().argc == 2);
    filename = master_test_suite().argv[1];

    ifstream in(filename, ios_base::in);

    if (!in) {
        cerr << "Error: Could not open input file: " << filename << endl;
    }

    string storage;         // We will read the contents here.
    in.unsetf(ios::skipws); // No white space skipping!
    copy(istream_iterator<char>(in),
         istream_iterator<char>(),
         back_inserter(storage));

    string::const_iterator iter = storage.begin();
    string::const_iterator end = storage.end();
    client::ast::Domain dom;

    using boost::spirit::x3::with;
    using client::parser::error_handler_tag;
    using client::parser::error_handler_type;

    error_handler_type error_handler(iter, end, std::cerr);

    auto const parser =
        with<error_handler_tag>(std::ref(error_handler))[domain()];

    bool r = phrase_parse(iter, end, parser, client::parser::skipper, dom);

    if (!(r && iter == end)) {
        std::cout << "-------------------------\n";
        std::cout << "Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
    }

    print(dom);
    BOOST_TEST(dom.name == "construction");
}
