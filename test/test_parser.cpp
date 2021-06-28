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
using namespace ast;
using boost::get;

BOOST_AUTO_TEST_CASE(test_parser) {

    string storage;

    // Test variable parsing
    auto v = parse<Variable>("?var", variable());
    BOOST_TEST(v.name == "var");

    // Test primitive type parsing
    // TODO See whether we need to reintroduce the client namespace
    auto pt = parse<PrimitiveType>("type", primitive_type());
    BOOST_TEST(pt == "type");

    // Test either type parsing
    auto et = parse<EitherType>("(either type0 type1)", either_type());
    BOOST_TEST(in(PrimitiveType{"type0"}, et));
    BOOST_TEST(in(PrimitiveType{"type1"}, et));

    // Test type parsing
    auto t = parse<Type>("type", type());
    BOOST_TEST(get<PrimitiveType>(t) == "type");

    t = parse<Type>("(either type0 type1)", type());
    BOOST_TEST(in("type0", get<EitherType>(et)));
    BOOST_TEST(in("type1", get<EitherType>(et)));

    // Test implicitly typed list of names
    auto tl = parse<TypedList<Name>>("t0 t1 t2", typed_list_names());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 0);
    BOOST_TEST((tl.implicitly_typed_list.value()[0] == "t0"));
    BOOST_TEST((tl.implicitly_typed_list.value()[1] == "t1"));
    BOOST_TEST((tl.implicitly_typed_list.value()[2] == "t2"));

    // Test explicitly typed list of names
    tl = parse<TypedList<Name>>("name0 name1 name2 - type", typed_list_names());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 1);
    BOOST_TEST(tl.implicitly_typed_list.value().size() == 0);
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[0] == "name0");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[1] == "name1");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[2] == "name2");
    BOOST_TEST(get<PrimitiveType>(tl.explicitly_typed_lists[0].type) == "type");

    // Test explicitly typed list with either type
    tl = parse<TypedList<Name>>("name0 name1 name2 - (either type0 type1)",
                                typed_list_names());
    BOOST_TEST(tl.explicitly_typed_lists.size() == 1);
    BOOST_TEST(tl.implicitly_typed_list.value().size() == 0);
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[0] == "name0");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[1] == "name1");
    BOOST_TEST(tl.explicitly_typed_lists[0].entries[2] == "name2");
    BOOST_TEST(in(PrimitiveType{"type0"},
                  get<EitherType>(tl.explicitly_typed_lists[0].type)));
    BOOST_TEST(in(PrimitiveType{"type1"},
                  get<EitherType>(tl.explicitly_typed_lists[0].type)));

    // Test atomic formula skeleton
    auto afs = parse<AtomicFormulaSkeleton>(
        "(predicate ?var0 ?var1 - type0 ?var2)", atomic_formula_skeleton());
    BOOST_TEST(afs.predicate.name == "predicate");
    BOOST_TEST(afs.variables.explicitly_typed_lists[0].entries[0].name ==
               "var0");
    BOOST_TEST(afs.variables.explicitly_typed_lists[0].entries[1].name ==
               "var1");
    BOOST_TEST(get<PrimitiveType>(
                   afs.variables.explicitly_typed_lists[0].type) == "type0");
    BOOST_TEST(afs.variables.implicitly_typed_list.value()[0].name == "var2");

    // Test requirements
    auto reqs = parse<vector<string>>("(:requirements :strips :typing)",
                                      requirements());
    BOOST_TEST(reqs[0] == "strips");
    BOOST_TEST(reqs[1] == "typing");

    // Test parsing atomic formula of terms
    auto aft = parse<AtomicFormula<Term>>("(predicate name ?variable)",
                                          atomic_formula_terms());
    BOOST_TEST(aft.predicate.name == "predicate");
    BOOST_TEST(get<Constant>(aft.args[0]).name == "name");
    BOOST_TEST(get<Variable>(aft.args[1]).name == "variable");

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

    auto dom = parse<Domain>(storage, domain());

    // Test parsing of domain name
    BOOST_TEST(dom.name == "construction");

    // Test requirements
    BOOST_TEST(dom.requirements[0] == "strips");
    BOOST_TEST(dom.requirements[1] == "typing");

    // Test constants
    BOOST_TEST(dom.constants.explicitly_typed_lists[0].entries[0] ==
               "mainsite");
    BOOST_TEST(get<PrimitiveType>(
                   dom.constants.explicitly_typed_lists[0].type) == "site");

    // Test parsing of predicates
    BOOST_TEST(dom.predicates.size() == 7);
    BOOST_TEST(dom.predicates[0].predicate.name == "walls-built");
    BOOST_TEST(
        dom.predicates[0].variables.explicitly_typed_lists[0].entries[0].name ==
        "s");
    BOOST_TEST(
        get<PrimitiveType>(
            dom.predicates[0].variables.explicitly_typed_lists[0].type) ==
        "site");

    // Test parsing of goal descriptions

    // Parse nil
    auto gd = parse<Sentence>("()", sentence());
    BOOST_TEST(get<Nil>(gd) == Nil());

    // Parse atomic formula of terms
    auto gd2 = parse<Sentence>("(predicate name ?variable)", sentence());
    auto atomic_formula_1 = get<AtomicFormula<Term>>(gd2);
    BOOST_TEST(atomic_formula_1.predicate.name == "predicate");
    auto constant_1 = get<Constant>(atomic_formula_1.args[0]);
    BOOST_TEST(constant_1.name == "name");

    // Test parsing literals of terms
    auto positive_literal_of_terms =
        parse<Literal<Term>>("(predicate constant ?variable)", literal_terms());
    BOOST_TEST(
        get<AtomicFormula<Term>>(positive_literal_of_terms).predicate.name ==
        "predicate");

    auto negative_literal_of_terms = parse<Literal<Term>>(
        "(not (predicate constant ?variable))", literal_terms());
    BOOST_TEST(get<NegativeLiteral<Term>>(negative_literal_of_terms)
                   .atomic_formula.predicate.name == "predicate");

    // Test and sentence parsing
    auto s = parse<Sentence>("(and () (predicate name ?variable))", sentence());
    auto as = get<AndSentence>(s);
    BOOST_TEST(as.sentences.size() == 2);
    BOOST_TEST(get<Nil>(as.sentences[0]) == Nil());

    auto af = get<AtomicFormula<Term>>(as.sentences[1]);
    BOOST_TEST(af.predicate.name == "predicate");
    BOOST_TEST(af.args.size() == 2);
    BOOST_TEST(get<Constant>(af.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af.args[1]).name == "variable");

    // TODO add tests for parsing or, not, imply and other complex sentences.
    auto s2 = parse<Sentence>("(or () (predicate name ?variable))", sentence());
    auto os = get<OrSentence>(s2);
    BOOST_TEST(os.sentences.size() == 2);
    BOOST_TEST(get<Nil>(os.sentences[0]) == Nil());

    auto af2 = get<AtomicFormula<Term>>(os.sentences[1]);
    BOOST_TEST(af2.predicate.name == "predicate");
    BOOST_TEST(af2.args.size() == 2);
    BOOST_TEST(get<Constant>(af2.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af2.args[1]).name == "variable");

    auto s3 = parse<Sentence>("(imply () (predicate name ?variable))", sentence());
    auto is = get<ImplySentence>(s3);
    BOOST_TEST(get<Nil>(is.sentence1) == Nil());

    auto af3 = get<AtomicFormula<Term>>(is.sentence2);
    BOOST_TEST(af3.predicate.name == "predicate");
    BOOST_TEST(af3.args.size() == 2);
    BOOST_TEST(get<Constant>(af3.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af3.args[1]).name == "variable");

    auto s4 = parse<Sentence>("(not (predicate name ?variable))", sentence());
    auto ns = get<NotSentence>(s4);

    auto af4 = get<AtomicFormula<Term>>(ns.sentence);
    BOOST_TEST(af4.predicate.name == "predicate");
    BOOST_TEST(af4.args.size() == 2);
    BOOST_TEST(get<Constant>(af4.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af4.args[1]).name == "variable");


    // TODO Salena: 3rd object, rock, is implicit. 
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:requirements :strips :typing)
            (:objects
                factory house - site
                adobe - material
                rock) ;testing implicitly-typed
;           (:init
;               (on-site adobe factory)
;               )   
;           (:goal
;               (on-site adobe house)      
                )
    )";


    auto prob = parse<Problem>(storage, problem());

    BOOST_TEST(prob.name == "adobe");
    BOOST_TEST(prob.domain_name == "construction");

    // Test requirements
    BOOST_TEST(prob.requirements[0] == "strips");
    BOOST_TEST(prob.requirements[1] == "typing");

    // Test objects
    BOOST_TEST(prob.objects.explicitly_typed_lists.size() == 2);
    
    BOOST_TEST(prob.objects.explicitly_typed_lists[0].entries[0] == "factory");
    BOOST_TEST(prob.objects.explicitly_typed_lists[0].entries[1] == "house");
    BOOST_TEST(boost::get<ast::PrimitiveType>(prob.objects.explicitly_typed_lists[0].type) == "site");
    
    BOOST_TEST(prob.objects.explicitly_typed_lists[1].entries[0] == "adobe");
    BOOST_TEST(boost::get<ast::PrimitiveType>(prob.objects.explicitly_typed_lists[1].type) == "material");

    BOOST_TEST(prob.objects.implicitly_typed_list.value()[0] == "rock");//default type = object

}
