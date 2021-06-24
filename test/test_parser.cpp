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
#include <boost/spirit/home/x3/support/ast/variant.hpp>

using boost::unit_test::framework::master_test_suite;
namespace x3 = boost::spirit::x3;
using namespace std;
using boost::get;

BOOST_AUTO_TEST_CASE(test_parser) {

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

    // Test explicitly typed list of names
    tl = parse<ast::TypedList<ast::Name>>("name0 name1 name2 - type",
                                          typed_list_names());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 1);
    BOOST_TEST(tl.implicitly_typed_list.value().size() == 0);
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[0] == "name0");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[1] == "name1");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[2] == "name2");
    BOOST_TEST(
        get<ast::PrimitiveType>(tl.explicitly_typed_lists[0].type).name ==
        "type");

    // Test explicitly typed list with either type
    tl = parse<ast::TypedList<ast::Name>>(
        "name0 name1 name2 - (either type0 type1)", typed_list_names());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 1);
    BOOST_TEST(tl.implicitly_typed_list.value().size() == 0);
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[0] == "name0");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[1] == "name1");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[2] == "name2");
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

    // Test requirements
    auto reqs = parse<vector<string>>("(:requirements :strips :typing)",
                                      requirements());
    BOOST_TEST(reqs[0] == "strips");
    BOOST_TEST(reqs[1] == "typing");

    // Test parsing atomic formula of terms
    auto aft = parse<ast::AtomicFormula<ast::Term>>(
        "(predicate name ?variable)", atomic_formula_terms());
    BOOST_TEST(aft.predicate.name == "predicate");
    BOOST_TEST(get<ast::Name>(aft.args[0]) == "name");
    BOOST_TEST(get<ast::Variable>(aft.args[1]).name == "variable");

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
    BOOST_TEST(
        dom.predicates[0].args.explicitly_typed_lists[0].entries[0].name ==
        "s");
    BOOST_TEST(get<ast::PrimitiveType>(
                   dom.predicates[0].args.explicitly_typed_lists[0].type)
                   .name == "site");

    // Test parsing of goal descriptions

    // Parse nil
    auto gd = parse<ast::GoalDescription>("()", goal_description());
    BOOST_TEST(boost::get<ast::Nil>(gd.value) == ast::Nil());

    // Parse atomic formula of terms
    auto gd2 = parse<ast::GoalDescription>("(predicate name ?variable)", goal_description());
    BOOST_TEST(boost::get<ast::AtomicFormula<ast::Term>>(gd2.value).predicate.name == "predicate");

    //auto as = parse<ast::GoalDescription>("(and () (predicate name ?variable))", goal_description());
    //BOOST_TEST(boost::get<ast::AtomicFormula<ast::Term>>(gd.children[1]).args.size() == 2);

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
