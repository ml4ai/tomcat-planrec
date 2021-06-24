#pragma once

#include "ast.hpp"
#include <boost/fusion/include/adapt_struct.hpp>

// We need to tell fusion about our domain structs to make them first-class
// fusion citizens. This has to be in global scope.

BOOST_FUSION_ADAPT_STRUCT(ast::Constant, name)
BOOST_FUSION_ADAPT_STRUCT(ast::Variable, name)
BOOST_FUSION_ADAPT_STRUCT(ast::PrimitiveType, name)
BOOST_FUSION_ADAPT_STRUCT(ast::EitherType, primitive_types)

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

BOOST_FUSION_ADAPT_STRUCT(ast::Predicate, name)
BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormulaSkeleton, predicate, args)
BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormula<ast::Term>, predicate, args)

BOOST_FUSION_ADAPT_STRUCT(ast::Nil)
BOOST_FUSION_ADAPT_STRUCT(ast::ConnectedSentence, args)

BOOST_FUSION_ADAPT_STRUCT(ast::Domain, name, requirements, types, constants, predicates)
BOOST_FUSION_ADAPT_STRUCT(ast::Problem, name, domain_name, requirements, objects)
