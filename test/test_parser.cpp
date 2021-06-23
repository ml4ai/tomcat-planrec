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
#include "parsing/parse.hpp"
#include "util.h"
#include <boost/optional.hpp>

using boost::unit_test::framework::master_test_suite;
using namespace std;


////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////
BOOST_AUTO_TEST_CASE(test_parser) {
    using boost::get;

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

    // Test implicitly typed list of names
    auto tl = parse<ast::TypedList<ast::Name>>("t0 t1 t2", typed_list_names());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 0);
    BOOST_TEST((tl.implicitly_typed_list.value()[0] == "t0"));
    BOOST_TEST((tl.implicitly_typed_list.value()[1] == "t1"));
    BOOST_TEST((tl.implicitly_typed_list.value()[2] == "t2"));

    // Test explicitly typed list of variables
    tl =
        parse<ast::TypedList<ast::Name>>("t0 t1 t2 - type", typed_list_names());
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
                                          typed_list_names());
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

    // Test atomic formula skeleton
    auto afs = parse<ast::AtomicFormulaSkeleton>(
        "(predicate ?var0 ?var1 - type0 ?var2)", atomic_formula_skeleton());
    BOOST_TEST(afs.predicate.name == "predicate");
    BOOST_TEST(afs.args.explicitly_typed_lists[0].entries[0].name == "var0");
    BOOST_TEST(afs.args.explicitly_typed_lists[0].entries[1].name == "var1");
    BOOST_TEST(
        get<ast::PrimitiveType>(afs.args.explicitly_typed_lists[0].type).name ==
        "type0");
    BOOST_TEST(afs.args.implicitly_typed_list.value()[0].name == "var2");

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

    // Test parsing of domain name
    BOOST_TEST(dom.name == "construction");

    // Test requirements
    BOOST_TEST(dom.requirements[0] == "strips");
    BOOST_TEST(dom.requirements[1] == "typing");

    // Test constants
    BOOST_TEST(dom.constants.explicitly_typed_lists[0].entries[0] ==
               "mainsite");
    BOOST_TEST(
        get<ast::PrimitiveType>(dom.constants.explicitly_typed_lists[0].type)
            .name == "site");

    // Test parsing of predicates
    BOOST_TEST(dom.predicates.size() == 7);
    BOOST_TEST(dom.predicates[0].predicate.name == "walls-built");
    BOOST_TEST(dom.predicates[0].args.explicitly_typed_lists[0].entries[0].name == "s");
    BOOST_TEST(get<ast::PrimitiveType>(dom.predicates[0].args.explicitly_typed_lists[0].type).name == "site");


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
     auto prob = parse<ast::Problem>(storage, problem());
     BOOST_TEST(prob.name == "adobe");
}
