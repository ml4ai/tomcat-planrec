#pragma once
#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/utility/annotate_on_success.hpp>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "domain.hpp"
#include "error_handler.hpp"

namespace parser {
    using ast::Constant, ast::Variable, ast::PrimitiveType, ast::EitherType,
          ast::Type, ast::ImplicitlyTypedList, ast::ExplicitlyTypedList, ast::TypedList,
          ast::Name;
        
    using boost::fusion::at_c;
    using x3::lexeme, x3::lit, x3::alnum, x3::_attr, x3::_val, x3::space,
        x3::eol, x3::rule;

    auto const name =
        lexeme[!lit('-') >> +(char_ - '?' - '(' - ')' - ':' - space)];
    auto const requirement = ':' >> name;

    // Rules
    rule<class TConstant, Constant> const constant = "constant";
    rule<class TVariable, Variable> const variable = "variable";
    rule<class TPrimitiveType, PrimitiveType> const primitive_type = "primitive_type";
    rule<class TEitherType, EitherType> const either_type = "either_type";
    rule<class TType, Type> const type = "type";
    rule<class TExplicitlyTypedList, ExplicitlyTypedList<Name>> const explicitly_typed_list = "explicitly_typed_list";
    rule<class TImplicitlyTypedList, ImplicitlyTypedList<Name>> const implicitly_typed_list = "implicitly_typed_list";
    rule<class TTypedList, TypedList<Name>> const typed_list = "typed_list";

    // Grammar
    auto const constant_def = name;
    auto const variable_def = '?' >> name;
    auto const primitive_type_def = name;
    auto const either_type_def = '(' >> lit("either") >> +primitive_type >> ')';
    auto const type_def = primitive_type | either_type; 

    auto const explicitly_typed_list_def = +name >> '-' >> type;
    BOOST_SPIRIT_DEFINE(explicitly_typed_list);

    auto const implicitly_typed_list_def = *name;
    BOOST_SPIRIT_DEFINE(implicitly_typed_list);

    auto const typed_list_def = *explicitly_typed_list >> -implicitly_typed_list;
    BOOST_SPIRIT_DEFINE(typed_list);

    BOOST_SPIRIT_DEFINE(constant, variable, primitive_type, either_type, type);


} // namespace parser

parser::constant_type constant() { return parser::constant; }
parser::variable_type variable() { return parser::variable; }
parser::primitive_type_type primitive_type() { return parser::primitive_type; }
parser::either_type_type either_type() { return parser::either_type; }
parser::type_type type() { return parser::type; }
parser::typed_list_type typed_list() { return parser::typed_list; }
