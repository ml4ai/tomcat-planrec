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
using namespace boost;
using namespace std;



class Print{

  public:
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
        cout << "  " << x << endl;
    }
    cout << endl;
    cout << "Actions:" << endl;
    for (auto x : dom.actions) {
        cout << x.name << endl;
        cout << "  parameters: " << endl;
        for (auto p : x.parameters) {
            cout << "  " << p << endl;
        }
        cout << endl;
        cout << endl; // Line between each action parsed
    }
    cout << endl;

    cout << "Constants:" << endl;
    for (auto constant : dom.constants) {
        cout << "  " << constant  << endl;;
    }
    cout << endl;
    cout << "Predicates:" << endl;
    for (auto x : dom.predicates) {
        cout << "  " << x.predicate;
        for (auto variable : x.variables) {
            cout << " " << variable;
        }
        cout << endl;
    }
    cout << endl;
  }// end print()

    void print(client::ast::Problem prob) {
        using namespace std;
        cout << "Problem Name: " << prob.name << endl;
        cout << "Problem Domain: " << prob.probDomain << endl;
        cout << "Requirements: " << endl;
        for (auto x : prob.requireDomain) {
            cout << '"' << x << '"' << endl;
        }
        cout << endl;
        cout << "Objects: " << endl;
        for (auto x : prob.objects) {
            cout << "  " << x << endl;
        }
        cout << endl;
  }//end print()
};// end Print class


////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////
BOOST_AUTO_TEST_CASE(test_parser) {
    using namespace std;
    typedef string::const_iterator iterator_type;
    using client::domain;
    using client::problem;

    using boost::spirit::x3::with;
    using client::parser::error_handler_tag;
    using client::parser::error_handler_type;

///// Parsing Domain:
    char const* domain_filename;
    char const* problem_filename;
    BOOST_TEST_REQUIRE(master_test_suite().argc == 3);
    domain_filename = master_test_suite().argv[1];
    problem_filename = master_test_suite().argv[2];

    // Overloading print() for domain and problem:
    Print data;

//domain_filename
    ifstream in(domain_filename, ios_base::in);

    if (!in) {
        cerr << "Error: Could not open input file: " << domain_filename << endl;
    }

    string storage;         // We will read the contents here.
    in.unsetf(ios::skipws); // No white space skipping!
    copy(istream_iterator<char>(in),
         istream_iterator<char>(),
         back_inserter(storage));

    string::const_iterator iter = storage.begin();
    string::const_iterator end = storage.end();
    client::ast::Domain dom;
    error_handler_type error_handler(iter, end, std::cerr);

    // Parsing Domain:
    auto const parser =
        with<error_handler_tag>(std::ref(error_handler))[domain()];

    bool r = phrase_parse(iter, end, parser, client::parser::skipper, dom);

    if (!(r && iter == end)) {
        std::cout << "-------------------------\n";
        std::cout << "Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
    }
    data.print(dom);

    BOOST_TEST(dom.name == "construction");

//problem_filename
    ifstream pin(problem_filename, ios_base::in);

    if (!pin) {
        cerr << "Error: Could not open input file: " << problem_filename << endl;
    }

    string pstorage;         
    in.unsetf(ios::skipws);
    copy(istream_iterator<char>(in),
         istream_iterator<char>(),
         back_inserter(pstorage));

    string::const_iterator piter = pstorage.begin();
    string::const_iterator pend = pstorage.end();
    client::ast::Problem prob;
    error_handler_type p_error_handler(piter, pend, std::cerr);

// Parsing Problem:
    auto const pParser =
        with<error_handler_tag>(std::ref(p_error_handler))[problem()];

    bool s = phrase_parse(piter, pend, pParser, client::parser::skipper, prob);

    if (!(s && piter == pend)) {
        std::cout << "-------------------------\n";
        std::cout << "Parsing failed\n";
        std::cout << "-------------------------\n";
        p_error_handler(piter, "Error!");
    }
    data.print(prob);

    BOOST_TEST(prob.name == "adobe");
}
