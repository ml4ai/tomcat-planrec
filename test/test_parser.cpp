#define BOOST_TEST_MODULE TestParser

#include <boost/test/included/unit_test.hpp>

#include <boost/variant/get.hpp>
#include <fstream>
#include <iostream>
#include <string>

#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/config.hpp"
#include "parsing/domain.hpp"
#include "parsing/error_handler.hpp"
#include "util.h"
#include <boost/optional.hpp>

using boost::unit_test::framework::master_test_suite;
using namespace std;

// void print(ast::Domain dom) {
// cout << "Name: " << dom.name << endl;
// cout << "Requirements: " << endl;
// for (auto x : dom.requirements) {
// cout << '"' << x << '"' << endl;
//}
// cout << endl;
// cout << "Types: " << endl;
// for (auto x : dom.types) {
// cout << "  " << x << endl;
//}
// cout << endl;
// cout << "Actions:" << endl;
// for (auto x : dom.actions) {
// cout << x.name << endl;
// cout << "  parameters: " << endl;
// for (auto p : x.parameters) {
// cout << "  " << p << endl;
//}
// cout << endl;
// cout << endl; // Line between each action parsed
//}
// cout << endl;

// cout << "Constants:" << endl;
// for (auto constant : dom.constants) {
// cout << "  " << constant << endl;
//;
//}
// cout << endl;
// cout << "Predicates:" << endl;
// for (auto x : dom.predicates) {
// cout << "  " << x.predicate;
// for (auto variable : x.variables) {
// cout << " " << variable;
//}
// cout << endl;
//}
// cout << endl;
//} // end print()

// void print(ast::Problem prob) {
// cout << "Problem Name: " << prob.name << endl;
// cout << "Problem Domain: " << prob.probDomain << endl;
// cout << "Requirements: " << endl;
// for (auto x : prob.requireDomain) {
// cout << '"' << x << '"' << endl;
//}
// cout << endl;
// cout << "Objects: " << endl;
// for (auto x : prob.objects) {
// cout << "  " << x << endl;
//}
// cout << endl;
//} // end print()

template <class T, class U> T parse(std::string storage, U parser) {
    using parser::error_handler_tag, parser::error_handler_type;
    string::const_iterator iter = storage.begin();
    string::const_iterator end = storage.end();
    error_handler_type error_handler(iter, end, cerr);
    T object;
    auto const error_handling_parser =
        with<error_handler_tag>(ref(error_handler))[parser];
    bool r =
        phrase_parse(iter, end, error_handling_parser, parser::skipper, object);
    if (!(r && iter == end)) {
        error_handler(iter, "Error!");
    }
    return object;
}

////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////
BOOST_AUTO_TEST_CASE(test_parser) {
    using parser::error_handler_tag, parser::error_handler_type;

    using boost::get;
    using boost::spirit::x3::with;

    string storage;

    // Test variable parsing
    auto v = parse<ast::Variable>("?var", variable());
    BOOST_TEST(v.name == "var");

    // Test primitive type parsing
    // TODO See whether we need to reintroduce the client namespace
    auto pt = parse<ast::PrimitiveType>("type", primitive_type());
    BOOST_TEST(pt.name == "type");

    // Test either type parsing
    auto et = parse<ast::EitherType>("(either type0 type1)", either_type());
    BOOST_TEST(in(ast::PrimitiveType{"type0"}, et.primitive_types));
    BOOST_TEST(in(ast::PrimitiveType{"type1"}, et.primitive_types));

    // Test type parsing
    auto t = parse<ast::Type>("type", type());
    BOOST_TEST(get<ast::PrimitiveType>(t).name == "type");

    t = parse<ast::Type>("(either type0 type1)", type());
    BOOST_TEST(in(ast::PrimitiveType{"type0"},
                  get<ast::EitherType>(et).primitive_types));
    BOOST_TEST(in(ast::PrimitiveType{"type1"},
                  get<ast::EitherType>(et).primitive_types));

    // Test implicitly typed list
    auto tl = parse<ast::TypedList<ast::Name>>("t0 t1 t2", typed_list());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 0);
    BOOST_TEST((tl.implicitly_typed_list.value()[0] == "t0"));
    BOOST_TEST((tl.implicitly_typed_list.value()[1] == "t1"));
    BOOST_TEST((tl.implicitly_typed_list.value()[2] == "t2"));

    // Test explicitly typed list
    tl = parse<ast::TypedList<ast::Name>>("t0 t1 t2 - type", typed_list());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 1);
    BOOST_TEST(tl.implicitly_typed_list.value().size() == 0);
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[0] == "t0");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[1] == "t1");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[2] == "t2");
    BOOST_TEST(
        get<ast::PrimitiveType>(tl.explicitly_typed_lists[0].type).name ==
        "type");

    // Test explicitly typed list with either type
    tl = parse<ast::TypedList<ast::Name>>("t0 t1 t2 - (either type0 type1)",
                                          typed_list());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 1);
    BOOST_TEST(tl.implicitly_typed_list.value().size() == 0);
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[0] == "t0");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[1] == "t1");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[2] == "t2");
    BOOST_TEST(in(ast::PrimitiveType{"type0"},
                  get<ast::EitherType>(tl.explicitly_typed_lists[0].type)
                      .primitive_types));
    BOOST_TEST(in(ast::PrimitiveType{"type1"},
                  get<ast::EitherType>(tl.explicitly_typed_lists[0].type)
                      .primitive_types));

    auto reqs = parse<vector<string>>("(:requirements :strips :typing)",
                                      requirements());
    BOOST_TEST(reqs[0] == "strips");
    BOOST_TEST(reqs[1] == "typing");

    storage = R"(
    ; Example domain for testing
        (define
            (domain construction)
            (:requirements :strips :typing)
            (:types
                site material - object
                bricks cables windows - material
            )
            ;(:constants mainsite - site)

            ;(:predicates
            ;    (walls-built ?s - site)
            ;    (windows-fitted ?s - site)
            ;    (foundations-set ?s - site)
            ;    (cables-installed ?s - site)
            ;    (site-built ?s - site)
            ;    (on-site ?m - material ?s - site)
            ;    (material-used ?m - material)
            ;)

            ;(:action BUILD-WALL
            ;    :parameters (?s - site ?b - bricks)
            ;    ;:precondition (()
            ;    ;:precondition (and
            ;        ;(on-site ?b ?s)
            ;        ;(foundations-set ?s)
            ;        ;(not (walls-built ?s))
            ;        ;(not (material-used ?b))
            ;    ;)
            ;    ;:effect (and
            ;        ;(walls-built ?s)
            ;        ;(material-used ?b)
               ;)
            ;)
        )
    )";

    auto dom = parse<ast::Domain>(storage, domain());
    BOOST_TEST(dom.name == "construction");
    BOOST_TEST(dom.requirements[0] == ":strips");
    BOOST_TEST(dom.requirements[1] == ":typing");

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
    // auto prob = parse<ast::Problem>(storage, problem());
    // BOOST_TEST(prob.name == "adobe");
}
