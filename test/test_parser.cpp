#define BOOST_TEST_MODULE TestParser

#include <boost/test/included/unit_test.hpp>

#include <fstream>
#include <iostream>
#include <string>

#include "parsing/api.hpp"
#include "parsing/ast.hpp"
#include "parsing/ast_adapted.hpp"
#include "parsing/parse.hpp"
#include "util.h"
#include <boost/optional.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>

using boost::unit_test::framework::master_test_suite;
namespace x3 = boost::spirit::x3;
using namespace ast;
using boost::get;
using std::string, std::vector, std::unordered_set;

std::string name(Term term) {
    return boost::apply_visitor([](const auto& t) { return t.name; }, term);
}

template <class T> bool equals(std::vector<T> x, std::vector<T> y) {
    return x == y;
}

// String variable that we will use to store inputs (make sure the tests in
// this module are not run in parallel!)
string storage;

BOOST_AUTO_TEST_CASE(test_type_parsing) {
    // Test type parsing
    auto t = parse<Type>("type");
    BOOST_TEST(boost::get<PrimitiveType>(t) == "type");

    t = parse<Type>("(either type0 type1)");
    BOOST_TEST(boost::get<EitherType>(t) ==
               unordered_set<string>({"type0", "type1"}));
}

BOOST_AUTO_TEST_CASE(test_fol_sentence_parsing) {
    // Test parsing of goal descriptions
    // Parse nil
    auto gd = parse<Sentence>("()");
    BOOST_TEST(boost::get<Nil>(gd) == Nil());

    // Parse atomic formula of terms
    auto gd2 = parse<Sentence>("(predicate name ?variable)");
    auto lit1 = boost::get<Literal<Term>>(gd2);
    BOOST_TEST(lit1.predicate == "predicate");
    BOOST_TEST(name(lit1.args[0]) == "name");

    // Testing connected sentence parsing

    // Test and sentence parsing
    auto s = parse<Sentence>("(and () (predicate name ?variable))");
    auto as = boost::get<ConnectedSentence>(s);
    BOOST_TEST(as.connector == "and");
    BOOST_TEST(as.sentences.size() == 2);
    BOOST_TEST(boost::get<Nil>(as.sentences[0]) == Nil());

    auto af = boost::get<Literal<Term>>(as.sentences[1]);
    BOOST_TEST(af.predicate == "predicate");
    BOOST_TEST(af.args.size() == 2);
    BOOST_TEST(name(af.args[0]) == "name");
    BOOST_TEST(name(af.args[1]) == "variable");

    // Test parsing literals of terms
    auto literal_of_terms =
        parse<Literal<Term>>("(predicate constant ?variable)");

    // Test parsing or sentence
    auto s2 = parse<Sentence>("(or () (predicate name ?variable))");
    auto os = boost::get<ConnectedSentence>(s2);
    BOOST_TEST(os.connector == "or");
    BOOST_TEST(os.sentences.size() == 2);
    BOOST_TEST(boost::get<Nil>(os.sentences[0]) == Nil());

    auto af2 = boost::get<Literal<Term>>(os.sentences[1]);
    BOOST_TEST(af2.predicate == "predicate");
    BOOST_TEST(af2.args.size() == 2);
    BOOST_TEST(name(af2.args[0]) == "name");
    BOOST_TEST(name(af2.args[1]) == "variable");

    auto s3 =
        parse<Sentence>("(imply () (predicate name ?variable))");
    auto is = boost::get<ImplySentence>(s3);
    BOOST_TEST(boost::get<Nil>(is.sentence1) == Nil());

    auto af3 = boost::get<Literal<Term>>(is.sentence2);
    BOOST_TEST(af3.predicate == "predicate");
    BOOST_TEST(af3.args.size() == 2);
    BOOST_TEST(name(af3.args[0]) == "name");
    BOOST_TEST(name(af3.args[1]) == "variable");

    auto s4 =
        parse<Sentence>("(not (predicate constant ?variable))");

    auto af4 = boost::get<NotSentence>(s4);
    auto af5 = boost::get<Literal<Term>>(af4.sentence);
    BOOST_TEST(af5.predicate == "predicate");
    BOOST_TEST(af5.args.size() == 2);
    BOOST_TEST(name(af5.args[0]) == "constant");
    BOOST_TEST(name(af5.args[1]) == "variable");

    auto s5 = parse<Sentence>("(forall (?variable) (predicate name ?variable))");
    auto fs = boost::get<QuantifiedSentence>(s5);
    BOOST_TEST(fs.quantifier == "forall");
    BOOST_TEST(fs.variables.implicitly_typed_list[0].name ==
               "variable");

    auto af_5 = boost::get<Literal<Term>>(fs.sentence);
    BOOST_TEST(af_5.predicate == "predicate");
    BOOST_TEST(af_5.args.size() == 2);
    BOOST_TEST(name(af_5.args[0]) == "name");
    BOOST_TEST(name(af_5.args[1]) == "variable");

    auto s6 = parse<Sentence>("(exists (?variable) (predicate name ?variable))");
    auto es = boost::get<QuantifiedSentence>(s6);
    BOOST_TEST(es.quantifier == "exists");
    BOOST_TEST(es.variables.implicitly_typed_list[0].name ==
               "variable");

    auto af6 = boost::get<Literal<Term>>(es.sentence);
    BOOST_TEST(af6.predicate == "predicate");
    BOOST_TEST(af6.args.size() == 2);
    BOOST_TEST(name(af6.args[0]) == "name");
    BOOST_TEST(name(af6.args[1]) == "variable");

    auto s7 = parse<Sentence>(R"(
        (imply
            (forall
                (?x)
                (forall
                    (?y)
                    (imply
                        (Animal ?y)
                        (Loves ?x ?y))))
            (exists (?y) (Loves ?y ?x)))
        )");
    auto cs = boost::get<ImplySentence>(s7);
    auto fs1 = boost::get<QuantifiedSentence>(cs.sentence1);
    BOOST_TEST(fs1.quantifier == "forall");
    BOOST_TEST(fs1.variables.implicitly_typed_list[0].name == "x");
    auto fs2 = boost::get<QuantifiedSentence>(cs.sentence2);
    BOOST_TEST(fs2.quantifier == "exists");
    BOOST_TEST(fs2.variables.implicitly_typed_list[0].name == "y");
}

BOOST_AUTO_TEST_CASE(test_domain_parsing) {
    // Test parsing of domain definition and its components
    // Domain from https://gki.informatik.uni-freiburg.de/competition/competition_status.html
    // Additional elements added to this domain for parser testing purposes
    // only, and may not make logical sense.

    storage = R"(
    (define (domain transport)
  (:requirements :negative-preconditions :hierarchy :typing)
  (:types
        location target locatable - object
        vehicle package - locatable
        capacity-number - object
  )
  (:constants surprise - package)

  (:predicates
     (road ?l1 ?l2 - location)
     (at ?x - locatable ?v - location)
     (in ?x - package ?v - vehicle)
     (capacity ?v - vehicle ?s1 - capacity-number)
     (capacity-predecessor ?s1 ?s2 - capacity-number)
  )

  ;; Abstract Tasks
  (:task deliver :parameters (?p - package ?l - location))
  (:task get-to :parameters (?v - vehicle ?l - location))
  (:task load :parameters (?v - vehicle ?l - location ?p - package))
  (:task unload :parameters (?v - vehicle ?l - location ?p - package))

  ;; Methods used to decompose tasks
  (:method m-deliver
    :parameters (?p - package ?l1 ?l2 - location ?v - vehicle)
    :task (deliver ?p ?l2)
     :ordered-subtasks (and
      (get-to ?v ?l1)
      (load ?v ?l1 ?p)
      (get-to ?v ?l2)
      (unload ?v ?l2 ?p))
  )

  (:method m-unload
    :parameters (?v - vehicle ?l - location ?p - package ?s1 ?s2 - capacity-number)
    :task (unload ?v ?l ?p)
    :subtasks (drop ?v ?l ?p ?s1 ?s2)
  )

  (:method m-load
    :parameters (?v - vehicle ?l - location ?p - package ?s1 ?s2 - capacity-number)
    :task (load  ?v ?l ?p)
    :subtasks (pick-up ?v ?l ?p ?s1 ?s2)
  )

  (:method m-drive-to
    :parameters (?v - vehicle ?l1 ?l2 - location)
    :task (get-to ?v ?l2)
    :subtasks (and
        (drive ?v ?l1 ?l2))
  )

  (:method m-drive-to-via
    :parameters (?v - vehicle ?l2 ?l3 - location)
    :task (get-to  ?v ?l3)
    :ordered-subtasks (and
        (get-to ?v ?l2)
        (drive ?v ?l2 ?l3))
  )

  (:method m-i-am-there
    :parameters (?v - vehicle ?l - location)
    :task (get-to  ?v ?l)
    :subtasks (and
        (noop ?v ?l))
  )

  (:action drive
    :parameters (?v - vehicle ?l1 ?l2 - location)
    :precondition (and
        (at ?v ?l1)
        (road ?l1 ?l2))
    :effect (and
        (not (at ?v ?l1))
        (at ?v ?l2))
  )

  (:action noop
    :parameters (?v - vehicle ?l2 - location)
    :precondition (at ?v ?l2)
    :effect ()
  )

 (:action pick-up
    :parameters (?v - vehicle ?l - location ?p - package ?s1 ?s2 - capacity-number)
    :precondition (and
        (at ?v ?l)
        (at ?p ?l)
        (capacity-predecessor ?s1 ?s2)
        (capacity ?v ?s2)
      )
    :effect (and
        (not (at ?p ?l))
        (in ?p ?v)
        (capacity ?v ?s1)
        (not (capacity ?v ?s2))
      )
  )

  (:action drop
    :parameters (?v - vehicle ?l - location ?p - package ?s1 ?s2 - capacity-number)
    :precondition (and
        (at ?v ?l)
        (in ?p ?v)
        (capacity-predecessor ?s1 ?s2)
        (capacity ?v ?s1)
      )
    :effect (and
        (not (in ?p ?v))
        (at ?p ?l)
        (capacity ?v ?s2)
        (not (capacity ?v ?s1))
      )
  )

)
    )";

    //Begin original test domain
    /*
        (define
            (domain transport)
            (:requirements :strips :typing)
            (:types site package - object
                    house factory - site
                    box letter - package)
            (:constants surprise - package)

            (:predicates
                (in-transit ?loc1 ?loc2 - site)
                (at ?box - package ?house - site)
                (tAt ?l))

            ;; Abstract tasks
            (:task deliver
             :parameters (?p - package ?s - site))

            (:task get-to
             :parameters (?s - site))

            ;; Methods
            (:method m-deliver
             :parameters (?p - package
                          ?lp ?ld - site)
             :task (deliver ?p ?ld)
             :precondition (or (tAt ?l)
                               (tAt ?s))

             :ordered-subtasks
                (and (get-to ?lp)
                     (pick-up ?ld ?p)
                     (get-to ?ld)
                     (drop ?ld ?p)))

            ;; Actions
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
*/
//end of original test domain

    auto dom = parse<Domain>(storage);

    // Test Domain Name:
    BOOST_TEST(dom.name == "transport");

    // Test requirements
    BOOST_TEST(equals(dom.requirements, {"negative-preconditions", "hierarchy", "typing"}));


    // Test constants
    BOOST_TEST(dom.constants.explicitly_typed_lists[0].entries[0] ==
               "surprise");
    BOOST_TEST(boost::get<PrimitiveType>(
                   dom.constants.explicitly_typed_lists[0].type) == "package");
    
/* TO DO AND UPDATE:
 *
 *

    // Test parsing of predicates
    BOOST_TEST(dom.predicates.size() == 3);
    BOOST_TEST(dom.predicates[0].predicate == "in-transit");
    BOOST_TEST(
        dom.predicates[0].variables.explicitly_typed_lists[0].entries[0].name ==
        "loc1");
    BOOST_TEST(
        boost::get<PrimitiveType>(
            dom.predicates[0].variables.explicitly_typed_lists[0].type) ==
        "site");

    // Test parsing of abstract tasks
    BOOST_TEST(dom.tasks[0].name == "deliver");
    auto taskpara1 = dom.tasks[0].parameters;
    BOOST_TEST(boost::get<PrimitiveType>(
                   taskpara1.explicitly_typed_lists[0].type) == "package");

    // Test methods and their components (totally-ordered):
    // Test methods name:
    BOOST_TEST(dom.methods[0].name == "m-deliver");

    // Test Methods Parameters:
    BOOST_TEST(boost::get<PrimitiveType>(
                   dom.methods[0].parameters.explicitly_typed_lists[0].type) ==
               "package");

    // Test method's task to be broken down. In the abstract task, 'task' is
    // defined similar to an action. Here, it is defined as <Literal<Term>>
    auto methodtask = dom.methods[0].task;
    BOOST_TEST(methodtask.name == "deliver");
    BOOST_TEST(boost::get<Variable>(methodtask.parameters[0]).name == "p");

    // Test parsing method's precondition:
    auto methodprec_f = dom.methods[0].precondition;
    auto methodprec_s = boost::get<ConnectedSentence>(methodprec_f);
    auto methodprec1_os = boost::get<Literal<Term>>(methodprec_s.sentences[0]);
    auto methodprec2_os = boost::get<Literal<Term>>(methodprec_s.sentences[1]);
    BOOST_TEST(methodprec1_os.predicate == "tAt");
    BOOST_TEST(name(methodprec2_os.args[0]) == "s");

    // Test parsing method optional ordered-subtasks (totally-ordered methods)
    auto osubtask_s = boost::get<MTask>(boost::get<vector<SubTask>>(
        dom.methods[0].task_network.subtasks.value().subtasks)[2]);
    BOOST_TEST(osubtask_s.name == "get-to");
    BOOST_TEST(name(osubtask_s.parameters[0]) == "ld");

    // Test parsing of domain actions and their components:
    // Test parsing action names
    auto actname1 = dom.actions[0].name;
    BOOST_TEST(actname1 == "drive");

    // Test parsing action parameters
    auto actpara1 = dom.actions[0].parameters;
    BOOST_TEST(boost::get<PrimitiveType>(
                   actpara1.explicitly_typed_lists[0].type) == "package");
    BOOST_TEST(boost::get<PrimitiveType>(
                   actpara1.explicitly_typed_lists[1].type) == "site");
    BOOST_TEST(actpara1.explicitly_typed_lists[0].entries[0].name == "box1");
    BOOST_TEST(actpara1.explicitly_typed_lists[1].entries[0].name == "loc1");

    // Test parsing action precondition
    auto actprec1_f = dom.actions[0].precondition;
    auto actprec1_s = boost::get<ConnectedSentence>(actprec1_f);
    auto actprec1_os = boost::get<Literal<Term>>(actprec1_s.sentences[0]);
    BOOST_TEST(actprec1_os.predicate == "tAt");
    BOOST_TEST(boost::get<Variable>(actprec1_os.args[0]).name == "loc1");

    // Test parsing action effect
    auto effect1_f = dom.actions[0].effect;
    auto effect1_s = boost::get<AndCEffect>(effect1_f);
    auto effect1_af = boost::get<Literal<Term>>(effect1_s.c_effects[0]);
    BOOST_TEST(effect1_af.predicate == "tAt");
    BOOST_TEST(boost::get<Variable>(effect1_af.args[0]).name == "loc1");

    auto effect1_af2_literal =
        boost::get<Literal<Term>>(effect1_s.c_effects[1]);
    BOOST_TEST(effect1_af2_literal.predicate == "tAt");
    BOOST_TEST(name(effect1_af2_literal.args[0]) == "loc2");

*
*/

}// end of testing the domain


BOOST_AUTO_TEST_CASE(test_problem_parsing) {
    //  Test parsing of problem definition and its components
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

    auto prob = parse<Problem>(storage);

    BOOST_TEST(prob.name == "adobe");
    BOOST_TEST(prob.domain_name == "construction");

    // Test requirements
    BOOST_TEST(equals(prob.requirements, {"strips", "typing"}));

    // Test objects
    BOOST_TEST(prob.objects.explicitly_typed_lists.size() == 2);

    BOOST_TEST(equals(prob.objects.explicitly_typed_lists[0].entries,
                      {"factory", "house"}));
    BOOST_TEST(boost::get<ast::PrimitiveType>(
                   prob.objects.explicitly_typed_lists[0].type) == "site");
    BOOST_TEST(prob.objects.explicitly_typed_lists[1].entries[0] == "adobe");

    BOOST_TEST(boost::get<ast::PrimitiveType>(
                   prob.objects.explicitly_typed_lists[1].type) == "material");
    BOOST_TEST(prob.objects.implicitly_typed_list[0] ==
               "rock"); // default type = object

    // Test initial state
    BOOST_TEST(boost::get<Init>(prob.init)[0].predicate == "on-site");
    BOOST_TEST(
        equals(boost::get<Init>(prob.init)[0].args, {"adobe", "factory"}));
}
