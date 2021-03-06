#pragma once

#include "ast.hpp"
#include <boost/fusion/include/adapt_struct.hpp>

// We need to tell fusion about our domain structs to make them first-class
// fusion citizens. This has to be in global scope.

BOOST_FUSION_ADAPT_STRUCT(ast::Constant, name)
BOOST_FUSION_ADAPT_STRUCT(ast::Variable, name)

BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormula<ast::Term>, predicate, args)
BOOST_FUSION_ADAPT_STRUCT(ast::Literal<ast::Term>, predicate, args)

BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormula<ast::Name>, predicate, args)
BOOST_FUSION_ADAPT_STRUCT(ast::Literal<ast::Name>, predicate, args)

// Typed list of names
BOOST_FUSION_ADAPT_STRUCT(ast::ExplicitlyTypedList<ast::Name>, entries, type)
BOOST_FUSION_ADAPT_STRUCT(ast::TypedList<ast::Name>,
                          explicitly_typed_lists,
                          implicitly_typed_list)

// Typed list of variables
BOOST_FUSION_ADAPT_STRUCT(ast::ExplicitlyTypedList<ast::Variable>,
                          entries,
                          type)
BOOST_FUSION_ADAPT_STRUCT(ast::TypedList<ast::Variable>,
                          explicitly_typed_lists,
                          implicitly_typed_list)

BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormulaSkeleton, predicate, variables)

BOOST_FUSION_ADAPT_STRUCT(ast::Nil)
BOOST_FUSION_ADAPT_STRUCT(ast::ConnectedSentence, connector, sentences)
BOOST_FUSION_ADAPT_STRUCT(ast::NotSentence, sentence)
BOOST_FUSION_ADAPT_STRUCT(ast::ImplySentence, sentence1, sentence2)
BOOST_FUSION_ADAPT_STRUCT(ast::QuantifiedSentence,
                          quantifier,
                          variables,
                          sentence)
BOOST_FUSION_ADAPT_STRUCT(ast::EqualsSentence, lhs, rhs)
BOOST_FUSION_ADAPT_STRUCT(ast::NotEqualsSentence, lhs, rhs)

BOOST_FUSION_ADAPT_STRUCT(ast::Domain,
                          name,
                          requirements,
                          types,
                          constants,
                          predicates,
                          tasks,
                          methods,
                          actions)
BOOST_FUSION_ADAPT_STRUCT(ast::ProblemHTN,
                          problem_class,
                          parameters,
                          task_network)
BOOST_FUSION_ADAPT_STRUCT(ast::Problem,
                          name,
                          domain_name,
                          requirements,
                          objects,
                          problem_htn,
                          init,
                          goal)
BOOST_FUSION_ADAPT_STRUCT(ast::WhenCEffect, gd, cond_effect)
BOOST_FUSION_ADAPT_STRUCT(ast::ForallCEffect, variables, effect)
BOOST_FUSION_ADAPT_STRUCT(ast::AndCEffect, c_effects)
BOOST_FUSION_ADAPT_STRUCT(ast::Action, name, parameters, precondition, effect)
BOOST_FUSION_ADAPT_STRUCT(ast::Task, name, parameters)
BOOST_FUSION_ADAPT_STRUCT(ast::MTask, name, parameters)
BOOST_FUSION_ADAPT_STRUCT(ast::Ordering, first, second)
BOOST_FUSION_ADAPT_STRUCT(ast::SubTaskWithId, id, subtask)
BOOST_FUSION_ADAPT_STRUCT(ast::MethodSubTasks, ordering_kw, subtasks)
BOOST_FUSION_ADAPT_STRUCT(ast::TaskNetwork, subtasks, orderings, constraints)
BOOST_FUSION_ADAPT_STRUCT(
    ast::Method, name, parameters, task, precondition, task_network)
