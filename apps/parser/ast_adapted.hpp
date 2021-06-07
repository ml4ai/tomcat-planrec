#pragma once

#include "ast.hpp"
#include <boost/fusion/include/adapt_struct.hpp>

// We need to tell fusion about our domain structs to make them first-class
// fusion citizens. This has to be in global scope.

BOOST_FUSION_ADAPT_STRUCT(client::ast::Entity, name, type)
BOOST_FUSION_ADAPT_STRUCT(client::ast::Variable, name, type)
BOOST_FUSION_ADAPT_STRUCT(client::ast::Action, name, parameters)
BOOST_FUSION_ADAPT_STRUCT(client::ast::AtomicFormulaSkeleton, predicate, variables)
BOOST_FUSION_ADAPT_STRUCT(
    client::ast::Domain, name, requirements, types, constants, predicates, actions)
