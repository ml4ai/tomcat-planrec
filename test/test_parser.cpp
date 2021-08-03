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

  (define (domain domain-htn)
	(:requirements :negative-preconditions :typing :hierarchy)
	(:types
		package - locatable
		capacity_number - object
		location - object
		target - object
		vehicle - locatable
		locatable - object
	)

    (:constants surprise - package)
	
    (:predicates
		(road ?arg0 - location ?arg1 - location)
		(at ?arg0 - locatable ?arg1 - location)
		(in ?arg0 - package ?arg1 ?arg2 - vehicle)
		(capacity ?arg0 - vehicle ?arg1 - capacity_number)
		(capacity_predecessor ?arg0 - capacity_number ?arg1 - capacity_number)
	)

	(:task deliver
		:parameters (?p - package ?l - location)
	)

	(:task get_to
		:parameters (?v - vehicle ?l - location)
	)


	(:method m_deliver_ordering_0
		:parameters (?loc1 - location ?loc2 - location ?p - package ?v - vehicle)
		:task (deliver ?p ?loc2) 

        :precondition (or
          (at ?l)
          (at ?s)
          )

        :subtasks (and
         (task0 (get_to ?v ?loc1))
         (task1 (load ?v ?loc1 ?p))
         (task2 (get_to ?v ?loc2))
         (task3 (unload ?v ?loc1 ?p))
         )

		:ordering (and
			( < task0 task1)
			( < task1 task2)
			( < task2 task3)
		)
	)

	(:method m_unload_ordering_0
		:parameters (?l - location ?p - package ?s1 - capacity_number ?s2 - capacity_number ?v - vehicle)
		:task (unload ?v ?l ?p)
		:subtasks (and
		 (task0 (drop ?v ?l ?p ?s1 ?s2))
		)
	)


	(:action pick_up
		:parameters (?v - vehicle ?l - location ?p - package ?s1 - capacity_number ?s2 - capacity_number)
		:precondition
			(and
				(at ?v ?l)
				(at ?p ?l)
				(capacity_predecessor ?s1 ?s2)
				(capacity ?v ?s2)
			)
		:effect
			(and
				(not (at ?p ?l))
				(in ?p ?v)
				(capacity ?v ?s1)
				(not (capacity ?v ?s2))
			)
	); end action pick_up
)

    )";



    auto dom = parse<Domain>(storage);

    // Test Domain Name:
    BOOST_TEST(dom.name == "domain-htn");

    // Test requirements
    BOOST_TEST(equals(dom.requirements, {"negative-preconditions", "typing", "hierarchy"}));

    // Test constants
    BOOST_TEST(dom.constants.explicitly_typed_lists[0].entries[0] ==
               "surprise");
    BOOST_TEST(boost::get<PrimitiveType>(
                   dom.constants.explicitly_typed_lists[0].type) == "package");
    
    // Test parsing of predicates
    BOOST_TEST(dom.predicates.size() == 5);
    BOOST_TEST(dom.predicates[2].predicate == "in");
    BOOST_TEST(dom.predicates[2].variables.explicitly_typed_lists[1].entries[0].name ==
        "arg1");
    BOOST_TEST(dom.predicates[2].variables.explicitly_typed_lists[1].entries[1].name ==
        "arg2");
    BOOST_TEST(
        boost::get<PrimitiveType>(
            dom.predicates[2].variables.explicitly_typed_lists[1].type) ==
        "vehicle");

    // Test parsing of abstract tasks
    BOOST_TEST(dom.tasks[0].name == "deliver");
    auto taskpara1 = dom.tasks[0].parameters;
    BOOST_TEST(boost::get<PrimitiveType>(
                   taskpara1.explicitly_typed_lists[0].type) == "package");

    // Test methods and their components (totally-ordered):
    // Test methods name:
    BOOST_TEST(dom.methods[0].name == "m_deliver_ordering_0");

    // Test Methods Parameters:
    BOOST_TEST(boost::get<PrimitiveType>(
                   dom.methods[0].parameters.explicitly_typed_lists[2].type) ==
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
    BOOST_TEST(methodprec1_os.predicate == "at");
    BOOST_TEST(name(methodprec2_os.args[0]) == "s");

    // Test Parsing Method's SubTasks:
    std::vector<ast::SubTask> subtask_v = boost::get<vector<SubTask>>(
        dom.methods[0].task_network.subtasks.value().subtasks);
    SubTask subtask_s = subtask_v[2];
    SubTaskWithId subtask_id = boost::get<SubTaskWithId>(subtask_s);
    BOOST_TEST(subtask_id.id == "task2");
    BOOST_TEST(subtask_id.subtask.name == "get_to");
    std::vector<ast::Term> subtask_p = subtask_id.subtask.parameters;
    BOOST_TEST(name(subtask_p[1]) == "loc2");
   
    // Test Parsing Method's Ordering:
    vector<ast::Ordering> ordering_v = boost::get<vector<Ordering>>(
        dom.methods[0].task_network.orderings.value());
    Ordering ordering_s = ordering_v[2];
    BOOST_TEST(ordering_s.second == "task3");

    // Test parsing of domain actions and their components:
    // Test parsing action names
    auto actname1 = dom.actions[0].name;
    BOOST_TEST(actname1 == "pick_up");

    // Test parsing action parameters
    auto actpara1 = dom.actions[0].parameters;
    BOOST_TEST(boost::get<PrimitiveType>(
                   actpara1.explicitly_typed_lists[0].type) == "vehicle");
    BOOST_TEST(boost::get<PrimitiveType>(
                   actpara1.explicitly_typed_lists[2].type) == "package");
    BOOST_TEST(actpara1.explicitly_typed_lists[0].entries[0].name == "v");
    BOOST_TEST(actpara1.explicitly_typed_lists[2].entries[0].name == "p");

    // Test parsing action precondition
    auto actprec1_f = dom.actions[0].precondition;
    auto actprec1_s = boost::get<ConnectedSentence>(actprec1_f);
    auto actprec1_os = boost::get<Literal<Term>>(actprec1_s.sentences[0]);
    BOOST_TEST(actprec1_os.predicate == "at");
    BOOST_TEST(boost::get<Variable>(actprec1_os.args[0]).name == "v");

    // Test parsing action effect
    auto effect1_f = dom.actions[0].effect;
    auto effect1_s = boost::get<AndCEffect>(effect1_f);
    auto effect1_af = boost::get<Literal<Term>>(effect1_s.c_effects[0]);
    BOOST_TEST(effect1_af.predicate == "at");
    BOOST_TEST(boost::get<Variable>(effect1_af.args[0]).name == "p");

}// end of testing the domain


BOOST_AUTO_TEST_CASE(test_problem_parsing) {
    //  Test parsing of problem definition and its components
    storage = R"(
        (define
            (problem delivery)
            (:domain domain_htn)
            (:requirements :strips :typing)

    	(:objects
	    	package_0 - package
		    package_1 - package
		    capacity_0 - capacity_number
		    capacity_1 - capacity_number
		    city_loc_0 - location
		    city_loc_1 - location
		    city_loc_2 - location
		    truck_0 - vehicle
            location
	    )
	(:htn
		;:parameters ()
		:parameters (?loc1 - location ?p - package ?v - vehicle)
		:subtasks (and
		 (task0 (deliver package_0 city_loc_0))
		 (task1 (deliver package_1 city_loc_2))
		)
		:ordering (and
			(< task0 task1)
		)
	)
	(:init
		(capacity_predecessor capacity_0 capacity_1)
		(road city_loc_0 city_loc_1)
		(road city_loc_1 city_loc_0)
		(road city_loc_1 city_loc_2)
		(road city_loc_2 city_loc_1)
		(at package_0 city_loc_1)
		(at package_1 city_loc_1)
		(at truck_0 city_loc_2)
		(capacity truck_0 capacity_1)
	)
          (:goal
                (and (at package_1 city_loc_2)
                     (at truck_1 city_loc_2)
                ))
 
); end problem definition
 )";

    auto prob = parse<Problem>(storage);

    BOOST_TEST(prob.name == "delivery");
    BOOST_TEST(prob.domain_name == "domain_htn");

    // Test requirements
    BOOST_TEST(equals(prob.requirements, {"strips", "typing"}));


    // Test initial state
    BOOST_TEST(boost::get<Init>(prob.init)[7].predicate == "at");
    BOOST_TEST(
        equals(boost::get<Init>(prob.init)[7].args, {"truck_0", "city_loc_2"}));

    // Test objects
    BOOST_TEST(prob.objects.explicitly_typed_lists.size() == 8);

    BOOST_TEST(equals(prob.objects.explicitly_typed_lists[0].entries,
                      {"package_0"}));
    BOOST_TEST(boost::get<ast::PrimitiveType>(
                   prob.objects.explicitly_typed_lists[0].type) == "package");
    BOOST_TEST(prob.objects.implicitly_typed_list[0] ==
               "location"); // default type = object

    // Test Problem HTN
    ProblemHTN  htn_f = prob.problem_htn; 
    BOOST_TEST(htn_f.problem_class == ":htn");
    auto htn_para = htn_f.parameters;
    BOOST_TEST(boost::get<PrimitiveType>(
          htn_para.explicitly_typed_lists[0].type) == "location");

    // Test Problem HTN Subtasks (brief test only)
    std::vector<SubTask> htn_subtasks = boost::get<vector<SubTask>>(
        htn_f.task_network.subtasks.value().subtasks); 
    SubTask htn_subtask_0 = htn_subtasks[0];
    SubTaskWithId htn_id = boost::get<SubTaskWithId>(htn_subtask_0);
    std::vector<Term> htn_sub_para = htn_id.subtask.parameters;
    BOOST_TEST(name(htn_sub_para[0]) == "package_0");

    // Test Problem Goal
    Sentence goal_f = prob.goal;
    ConnectedSentence goal_s = boost::get<ConnectedSentence>(goal_f);
    auto goal_1 = boost::get<Literal<Term>>(goal_s.sentences[0]);
    BOOST_TEST(goal_1.predicate == "at");
    BOOST_TEST(name(goal_1.args[1]) == "city_loc_2");
}
