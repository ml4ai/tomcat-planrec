#pragma once

#include "ast.hpp"
#include <boost/fusion/include/adapt_struct.hpp>

// We need to tell fusion about our domain structs to make them first-class
// fusion citizens. This has to be in global scope.

BOOST_FUSION_ADAPT_STRUCT(ast::Constant, name)
BOOST_FUSION_ADAPT_STRUCT(ast::Variable, name)
BOOST_FUSION_ADAPT_STRUCT(ast::PrimitiveType, name)
BOOST_FUSION_ADAPT_STRUCT(ast::EitherType, primitive_types)
//BOOST_FUSION_ADAPT_STRUCT(ast::Action, name, parameters)
//BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormula<ast::Variable>, predicate, args)
//BOOST_FUSION_ADAPT_STRUCT(ast::GoalDescription, entries)
//BOOST_FUSION_ADAPT_STRUCT(ast::AtomicFormulaSkeleton, predicate, variables)
//BOOST_FUSION_ADAPT_STRUCT(
    //ast::Domain, name, requirements, types, constants, predicates, actions)
//BOOST_FUSION_ADAPT_STRUCT(ast::Problem, name, probDomain, requireDomain, objects)
