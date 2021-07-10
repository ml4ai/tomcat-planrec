#pragma once

#include "ast.hpp"
#include <boost/fusion/include/adapt_struct.hpp>

// We need to tell fusion about our domain structs to make them first-class
// fusion citizens. This has to be in global scope.

BOOST_FUSION_ADAPT_STRUCT(ast::Constant, name)
BOOST_FUSION_ADAPT_STRUCT(ast::Variable, name)
BOOST_FUSION_ADAPT_STRUCT(ast::Literal<ast::Term>, predicate, args)

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
BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormula<ast::Term>, predicate, args)

BOOST_FUSION_ADAPT_STRUCT(ast::Nil)
BOOST_FUSION_ADAPT_STRUCT(ast::ConnectedSentence, connector, sentences)
BOOST_FUSION_ADAPT_STRUCT(ast::NotSentence, sentence)
BOOST_FUSION_ADAPT_STRUCT(ast::ImplySentence, sentence1, sentence2)
BOOST_FUSION_ADAPT_STRUCT(ast::ExistsSentence, variables, sentence)
BOOST_FUSION_ADAPT_STRUCT(ast::ForallSentence, variables, sentence)

BOOST_FUSION_ADAPT_STRUCT(ast::Domain, name, requirements, types, constants, predicates, tasks, actions)
BOOST_FUSION_ADAPT_STRUCT(ast::Problem, name, domain_name, requirements, objects, init, goal)
BOOST_FUSION_ADAPT_STRUCT(ast::Action, name, parameters, precondition, effect)
BOOST_FUSION_ADAPT_STRUCT(ast::Task, name, parameters)
