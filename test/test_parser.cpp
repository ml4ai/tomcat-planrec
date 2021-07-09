#define BOOST_TEST_MODULE TestParser

#include <boost/test/included/unit_test.hpp>

#include <boost/variant/get.hpp>
#include <fstream>
#include <iostream>
#include <string>

#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
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

    // TEST PARSING OF DATA STRUCTURES

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
    BOOST_TEST(in("type0", et));
    BOOST_TEST(in("type1", et));

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

    // Test explicitly typed list of variables
    auto vvl = parse<TypedList<Variable>>("?var0 ?var1 ?var2 - type",
                                          typed_list_variables());
    BOOST_TEST(vvl.explicitly_typed_lists[0].entries[0].name == "var0");
    BOOST_TEST(vvl.explicitly_typed_lists[0].entries[1].name == "var1");
    BOOST_TEST(vvl.explicitly_typed_lists[0].entries[2].name == "var2");
    BOOST_TEST(get<PrimitiveType>(vvl.explicitly_typed_lists[0].type) ==
               "type");

    // Test atomic formula skeleton
    auto afs = parse<AtomicFormulaSkeleton>(
        "(predicate ?var0 ?var1 - type0 ?var2)", atomic_formula_skeleton());
    BOOST_TEST(afs.predicate == "predicate");
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
    BOOST_TEST(aft.predicate == "predicate");
    BOOST_TEST(get<Constant>(aft.args[0]).name == "name");
    BOOST_TEST(get<Variable>(aft.args[1]).name == "variable");

    // Test parsing of goal descriptions
    // Parse nil
    auto gd = parse<Sentence>("()", sentence());
    BOOST_TEST(get<Nil>(gd) == Nil());

    // Parse atomic formula of terms
    auto gd2 = parse<Sentence>("(predicate name ?variable)", sentence());
    auto lit1 = get<Literal<Term>>(gd2);
    BOOST_TEST(lit1.predicate == "predicate");
    auto constant_1 = get<Constant>(lit1.args[0]);
    BOOST_TEST(constant_1.name == "name");

    // Test and sentence parsing
    auto s = parse<Sentence>("(and () (predicate name ?variable))", sentence());
    auto as = get<ConnectedSentence>(s);
    BOOST_TEST(as.connector == "and");
    BOOST_TEST(as.sentences.size() == 2);
    BOOST_TEST(get<Nil>(as.sentences[0]) == Nil());

    auto af = get<Literal<Term>>(as.sentences[1]);
    BOOST_TEST(af.predicate == "predicate");
    BOOST_TEST(af.args.size() == 2);
    BOOST_TEST(get<Constant>(af.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af.args[1]).name == "variable");

    // Test parsing literals of terms
    auto literal_of_terms =
        parse<Literal<Term>>("(predicate constant ?variable)", literal_terms());
    BOOST_TEST(literal_of_terms.predicate == "predicate");

    // Test parsing or sentence
    auto s2 = parse<Sentence>("(or () (predicate name ?variable))", sentence());
    auto os = get<ConnectedSentence>(s2);
    BOOST_TEST(os.sentences.size() == 2);
    BOOST_TEST(get<Nil>(os.sentences[0]) == Nil());

    auto af2 = get<Literal<Term>>(os.sentences[1]);
    BOOST_TEST(af2.predicate == "predicate");
    BOOST_TEST(af2.args.size() == 2);
    BOOST_TEST(get<Constant>(af2.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af2.args[1]).name == "variable");

    auto s3 =
        parse<Sentence>("(imply () (predicate name ?variable))", sentence());
    auto is = get<ImplySentence>(s3);
    BOOST_TEST(get<Nil>(is.sentence1) == Nil());

    auto af3 = get<Literal<Term>>(is.sentence2);
    BOOST_TEST(af3.predicate == "predicate");
    BOOST_TEST(af3.args.size() == 2);
    BOOST_TEST(get<Constant>(af3.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af3.args[1]).name == "variable");

    auto s4 =
        parse<Sentence>("(not (predicate constant ?variable))", sentence());

    auto af4 = get<NotSentence>(s4);
    auto af5 = get<Literal<Term>>(af4.sentence);
    BOOST_TEST(af5.predicate == "predicate");
    BOOST_TEST(af5.args.size() == 2);
    BOOST_TEST(get<Constant>(af5.args[0]).name == "constant");
    BOOST_TEST(get<Variable>(af5.args[1]).name == "variable");

    auto s5 = parse<Sentence>("(forall (?variable) (predicate name ?variable))",
                              sentence());
    auto fs = get<ForallSentence>(s5);
    BOOST_TEST(fs.variables.implicitly_typed_list.value()[0].name ==
               "variable");

    auto af_5 = get<Literal<Term>>(fs.sentence);
    BOOST_TEST(af_5.predicate == "predicate");
    BOOST_TEST(af_5.args.size() == 2);
    BOOST_TEST(get<Constant>(af_5.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af_5.args[1]).name == "variable");

    auto s6 = parse<Sentence>("(exists (?variable) (predicate name ?variable))",
                              sentence());
    auto es = get<ExistsSentence>(s6);
    BOOST_TEST(es.variables.implicitly_typed_list.value()[0].name ==
               "variable");

    auto af6 = get<Literal<Term>>(es.sentence);
    BOOST_TEST(af6.predicate == "predicate");
    BOOST_TEST(af6.args.size() == 2);
    BOOST_TEST(get<Constant>(af6.args[0]).name == "name");
    BOOST_TEST(get<Variable>(af6.args[1]).name == "variable");

    auto s7 =
        parse<Sentence>("(imply (forall (?x) (forall (?y) (imply (Animal ?y) (Loves ?x ?y)))) (exists (?y) (Loves ?y ?x)))",
                        sentence());
    auto cs = get<ImplySentence>(s7);
    auto fs1 = get<ForallSentence>(cs.sentence1);
    BOOST_TEST(fs1.variables.implicitly_typed_list.value()[0].name == "x");
    auto fs2 = get<ExistsSentence>(cs.sentence2);
    BOOST_TEST(fs2.variables.implicitly_typed_list.value()[0].name == "y");

    // TEST PARSING OF DOMAIN DEFINITION AND ITS COMPONENTS

    storage = R"(
        (define 
            (domain transport)
            (:requirements :strips :typing)
            (:types site package - object
                    house factory - site
                    box letter - package)
            (:constants surprise - package)

            (:predicates
                (in-transit ?loc1 ?loc2 - site)
                (at ?box - package ?house - site))

            (:task deliver
                :parameters 
                    (?p - package ?s - site))

            (:task get-to
               :parameters (?s - site))
            
            (:action drive
                :parameters 
                    (?box1 ?box2 - package
                     ?loc1 ?loc2 - site)
              :precondition 
                    (and (tAt ?loc1)
                         (in-transit ?loc1 ?loc2))
              :effect
                    (and (tAt ?loc1)
                         (not (tAt ?loc2)))
              ); end action drive
          );end define domain
    )";

/*** To add to HDDL Domain ***
 *
;            (:method m-deliver
;              :parameters (?p - package
;                           ?lp ?ld - site)
;              :task (deliver ?p ?ld)
;              :ordered-subtasks 
;                (and (get-to ?lp)
;                (pick-up ?ld ?p)
;                (get-to ?ld)
;                (drop ?ld ?p)))
;            
;            (:method m-drive-to-via
;              :parameters (?li ?ld - site)
;              :task (get-to ?ld)
;              :subtasks 
;                (and (t1 (get-to ?li))
;                     (t2 (drive ?li ld)))
;              :ordering 
;                (and (t1 < t2)))
;            
;            (:method m-already-there
;              :parameters (?l - site)
;              :task (get-to ?l)
;              :precondition (tAt ?l)
;              :subtasks ())
;            
;            (:method m-direct
;              :parameters (?ls ?ls - site)
;              :task (get-to ?ld)
;              :constraints ;not effects or precs!
;                (not (= ?li ?ld))
;              :subtasks (drive ?ls ?d))
;
*****/ // end what to add to HDDL parser

    auto dom = parse<Domain>(storage, domain());

    // Test Domain Name:
    BOOST_TEST(dom.name == "transport");

    // Test requirements
    BOOST_TEST(dom.requirements[0] == "strips");
    BOOST_TEST(dom.requirements[1] == "typing");

    // Test constants
    BOOST_TEST(dom.constants.explicitly_typed_lists[0].entries[0] ==
               "surprise");
    BOOST_TEST(get<PrimitiveType>(
                   dom.constants.explicitly_typed_lists[0].type) == "package");

    // Test parsing of predicates
    BOOST_TEST(dom.predicates.size() == 2);
    BOOST_TEST(dom.predicates[0].predicate == "in-transit");
    BOOST_TEST(dom.predicates[0].variables.explicitly_typed_lists[0].entries[0].name == "loc1");
    BOOST_TEST(get<PrimitiveType>(
        dom.predicates[0].variables.explicitly_typed_lists[0].type) == "site");
 
 
    // Test Parsing of DOMAIN ACTIONS and their components:
    // Test Parsing Action Names
    auto actname1 = dom.actions[0].name;
    BOOST_TEST(actname1 == "drive");

    // Test Parsing Action Parameters
    auto actpara1 = dom.actions[0].parameters;
    BOOST_TEST(get<PrimitiveType>(actpara1.explicitly_typed_lists[0].type) ==
               "package");
    BOOST_TEST(get<PrimitiveType>(actpara1.explicitly_typed_lists[1].type) ==
               "site");
    BOOST_TEST(actpara1.explicitly_typed_lists[0].entries[0].name == "box1");
    BOOST_TEST(actpara1.explicitly_typed_lists[1].entries[0].name == "loc1");

    // Test Parsing Action Precondition
    auto actprec1_f = dom.actions[0].precondition;
    auto actprec1_s = get<ConnectedSentence>(actprec1_f);
    auto actprec1_os = get<Literal<Term>>(actprec1_s.sentences[0]);
    BOOST_TEST(actprec1_os.predicate == "tAt");
    BOOST_TEST(get<Variable>(actprec1_os.args[0]).name == "loc1");


    // Test Parsing Action Effect
    auto effect1_f = dom.actions[0].effect;
    auto effect1_s = get<ConnectedSentence>(effect1_f);
    auto effect1_af = get<Literal<Term>>(effect1_s.sentences[0]);
    BOOST_TEST(effect1_af.predicate == "tAt");
    BOOST_TEST(get<Variable>(effect1_af.args[0]).name == "loc1");

    auto effect1_af2 = get<NotSentence>(effect1_s.sentences[1]);
    auto effect1_af2_literal = get<Literal<Term>>(effect1_af2.sentence);
    BOOST_TEST(effect1_af2_literal.predicate == "tAt");
    BOOST_TEST(get<Variable>(effect1_af2_literal.args[0]).name == "loc2");



//            (:task deliver 
//              :parameters (?p - package ?l - site))

    //Test Parsing Abstract Tasks
    
















    //  TEST PARSING OF PROBLEM DEFINITION AND ITS COMPONENTS
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:requirements :strips :typing)
            (:objects
                factory house - site
                adobe - material
                rock) ;testing implicitly-typed
           (:init
               (on-site adobe factory)
               )
          (:goal
               (and (off-site adobe1 factory1)
                    (on-site adobe2 house2)
               ))
        );end define
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
    BOOST_TEST(get<ast::PrimitiveType>(
                   prob.objects.explicitly_typed_lists[0].type) == "site");
    BOOST_TEST(prob.objects.explicitly_typed_lists[1].entries[0] == "adobe");

    BOOST_TEST(get<ast::PrimitiveType>(
                   prob.objects.explicitly_typed_lists[1].type) == "material");
    BOOST_TEST(prob.objects.implicitly_typed_list.value()[0] ==
               "rock"); // default type = object

    // Test initial state
    BOOST_TEST(get<Literal<Term>>(prob.init).predicate == "on-site");
    BOOST_TEST(get<Constant>(get<Literal<Term>>(prob.init).args[0]).name ==
               "adobe");
    BOOST_TEST(get<Constant>(get<Literal<Term>>(prob.init).args[1]).name ==
               "factory");

    // Test problem goal
    // Testing ConnectedSentences
    auto goal_as = get<ConnectedSentence>(
        prob.goal); // We know this is a ConnectedSentence
    BOOST_TEST(goal_as.sentences.size() == 2); // that containing two terms
    auto goal_af = get<Literal<Term>>(goal_as.sentences[0]); // first predicate
    auto goal_af2 =
        get<Literal<Term>>(goal_as.sentences[1]); // second predicate
    BOOST_TEST(goal_af.predicate == "off-site");
    BOOST_TEST(goal_af2.predicate == "on-site");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_as.sentences[0]).args[0]).name ==
        "adobe1");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_as.sentences[0]).args[1]).name ==
        "factory1");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_as.sentences[1]).args[0]).name ==
        "adobe2");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_as.sentences[1]).args[1]).name ==
        "house2");

    // Testing Problems with goal definitions corresponding to FOL Sentences of
    // different kinds. The 'storage' variable is redefined to only include
    // required components (problem, domain) and the goal, which demonstrates
    // the FOL variation.
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:objects
                factory house - site
                adobe - material
                rock) ;testing implicitly-typed
           (:init
               (on-site adobe factory))
            (:goal
               (or (off-site adobe3 factory3)
                   (on-site adobe4 house4)))
        );end define
    )";

    prob = parse<Problem>(storage, problem());

    // Testing ConnectedSentences
    auto goal_os = get<ConnectedSentence>(
        prob.goal); // we know this is an ConnectedSentence
    BOOST_TEST(goal_os.connector == "or");     // Test connector
    BOOST_TEST(goal_os.sentences.size() == 2); // containing two terms
    auto goal_of = get<Literal<Term>>(goal_os.sentences[0]); // first predicate
    auto goal_of2 =
        get<Literal<Term>>(goal_os.sentences[1]); // second predicate
    BOOST_TEST(goal_of.predicate == "off-site");
    BOOST_TEST(goal_of2.predicate == "on-site");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_os.sentences[0]).args[0]).name ==
        "adobe3");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_os.sentences[0]).args[1]).name ==
        "factory3");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_os.sentences[1]).args[0]).name ==
        "adobe4");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(goal_os.sentences[1]).args[1]).name ==
        "house4");

    // Testing NotSentences
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:requirements :strips :typing)
            (:objects
                factory house - site
                adobe - material
                rock) ;testing implicitly-typed
            (:init
               (on-site adobe factory))
            (:goal
                (not (on-site adobe3 factory3)))
        );end define
    )";

    prob = parse<Problem>(storage, problem());

    auto goal_ns = get<Literal<Term>>(get<NotSentence>(prob.goal).sentence);
    BOOST_TEST(goal_ns.predicate == "on-site");
    BOOST_TEST(goal_ns.args.size() == 2);
    BOOST_TEST(get<Constant>(goal_ns.args[0]).name == "adobe3");
    BOOST_TEST(get<Constant>(goal_ns.args[1]).name == "factory3");

    // Testing Imply Sentence
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:init
               (on-site adobe factory))
            (:goal
                (imply (on-site adobe3 factory3)
                       (off-site adobe3 house))
            )
        );end define
    )";

    prob = parse<Problem>(storage, problem());
    auto imply_s = get<ImplySentence>(prob.goal);
    auto imply_f = get<Literal<Term>>(imply_s.sentence1);
    auto imply_f2 = get<Literal<Term>>(imply_s.sentence2);
    BOOST_TEST(imply_f.predicate == "on-site");
    BOOST_TEST(imply_f2.predicate == "off-site");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(imply_s.sentence1).args[0]).name ==
        "adobe3");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(imply_s.sentence1).args[1]).name ==
        "factory3");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(imply_s.sentence2).args[0]).name ==
        "adobe3");
    BOOST_TEST(
        get<Constant>(get<Literal<Term>>(imply_s.sentence2).args[1]).name ==
        "house");

    // Testing ExistsSentence --and-- AndSentence (ConnectedSentence)
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:objects
                factory house - site
                adobe - material
                rock) ;testing implicitly-typed
            (:init
               (on-site adobe factory))
            (:goal
                (exists (?var1) 
                        (and (pred1 ar1 ?var2)
                             (pred1 ar2 ?var3)))
            );end goal
        );end define
    )";

    prob = parse<Problem>(storage, problem());
    auto ef = get<ExistsSentence>(prob.goal);

    BOOST_TEST(ef.variables.implicitly_typed_list.value()[0].name == "var1");

    auto connected = get<ConnectedSentence>(ef.sentence); // trial

    auto es1 = get<Literal<Term>>(connected.sentences[0]);
    auto es2 = get<Literal<Term>>(connected.sentences[1]);
    BOOST_TEST(es1.predicate == "pred1");
    BOOST_TEST(get<Constant>(es1.args[0]).name == "ar1");
    BOOST_TEST(get<Variable>(es2.args[1]).name == "var3");

    // Testing ForallSentence --and-- NotSentence
    storage = R"(
        (define
            (problem adobe)
            (:domain construction)
            (:objects
                factory house - site
                adobe - material
                rock) ;testing implicitly-typed
            (:init
               (on-site adobe factory))
            (:goal
                (forall (?var1) 
                        (not (pred1 ar1 ?var2)))
            );end goal
        );end define
    )";

    prob = parse<Problem>(storage, problem());
    auto fef = get<ForallSentence>(prob.goal);

    BOOST_TEST(fef.variables.implicitly_typed_list.value()[0].name == "var1");
    auto fes = get<Literal<Term>>(get<NotSentence>(fef.sentence).sentence);
    BOOST_TEST(fes.predicate == "pred1");
    BOOST_TEST(get<Constant>(fes.args[0]).name == "ar1");
    BOOST_TEST(get<Variable>(fes.args[1]).name == "var2");

}
