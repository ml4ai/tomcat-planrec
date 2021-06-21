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
using namespace std;

void print(client::ast::Domain dom) {
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
        cout << "  " << constant << endl;
        ;
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
} // end print()

void print(client::ast::Problem prob) {
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
} // end print()

////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////
BOOST_AUTO_TEST_CASE(test_parser) {
    typedef string::const_iterator iterator_type;
    using client::domain;
    using client::problem;

    using boost::spirit::x3::with;
    using client::parser::error_handler_tag;
    using client::parser::error_handler_type;

    string storage;
    storage = R"(
    ; Example domain for testing
        (define
            (domain construction)
            (:requirements :strips :typing)
            (:types
                site material - object
                bricks cables windows - material
            )
            (:constants mainsite - site)

            (:predicates
                (walls-built ?s - site)
                (windows-fitted ?s - site)
                (foundations-set ?s - site)
                (cables-installed ?s - site)
                (site-built ?s - site)
                (on-site ?m - material ?s - site)
                (material-used ?m - material)
            )

            (:action BUILD-WALL
                :parameters (?s - site ?b - bricks)
                ;:precondition (()
                ;:precondition (and
                    ;(on-site ?b ?s)
                    ;(foundations-set ?s)
                    ;(not (walls-built ?s))
                    ;(not (material-used ?b))
                ;)
                ;:effect (and
                    ;(walls-built ?s)
                    ;(material-used ?b)
                ;)
            )
        )
        )";

    string::const_iterator iter = storage.begin();
    string::const_iterator end = storage.end();

    error_handler_type error_handler(iter, end, std::cerr);

    client::ast::Domain dom;
    // Parsing Domain:
    auto const domain_parser =
        with<error_handler_tag>(std::ref(error_handler))[domain()];

    bool r =
        phrase_parse(iter, end, domain_parser, client::parser::skipper, dom);

    BOOST_TEST(dom.name == "construction");

    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:requirements :strips :typing)
            (:objects
                factory house - site
                adobe - material)
        )
    )";

    // Need to reset iter and end for every new string.
    iter = storage.begin();
    end = storage.end();

    client::ast::Problem prob;

    // Parsing Problem:
    auto const problem_parser =
        with<error_handler_tag>(std::ref(error_handler))[problem()];

    r = phrase_parse(iter, end, problem_parser, client::parser::skipper, prob);

    BOOST_TEST(prob.name == "adobe");
}
