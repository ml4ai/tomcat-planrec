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
        ast::Type, ast::ImplicitlyTypedList, ast::ExplicitlyTypedList,
        ast::TypedList, ast::Name;

    using boost::fusion::at_c;
    using x3::lexeme, x3::lit, x3::alnum, x3::_attr, x3::_val, x3::space,
        x3::eol, x3::rule;

    auto const name =
        lexeme[!lit('-') >> +(char_ - '?' - '(' - ')' - ':' - space)];

    // Rules
    rule<class TConstant, Constant> const constant = "constant";
    rule<class TVariable, Variable> const variable = "variable";
    rule<class TPrimitiveType, PrimitiveType> const primitive_type =
        "primitive_type";
    rule<class TEitherType, EitherType> const either_type = "either_type";
    rule<class TType, Type> const type = "type";
    rule<class TExplicitlyTypedList, ExplicitlyTypedList<Name>> const
        explicitly_typed_list = "explicitly_typed_list";
    rule<class TImplicitlyTypedList, ImplicitlyTypedList<Name>> const
        implicitly_typed_list = "implicitly_typed_list";
    rule<class TTypedList, TypedList<Name>> const typed_list = "typed_list";
    rule<class TTypes, TypedList<Name>> const types = "types";
    rule<class Predicate, Name> const predicate = "predicate";
    rule<class TDomain, ast::Domain> const domain = "domain";
    rule<class TRequirements, std::vector<Name>> const requirements =
        "requirements";
    rule<class TRequirement, std::vector<Name>> const requirement =
        "requirement";

    auto const requirement_def = ':' >> name;
    auto const predicate_def = name;
    auto const requirements_def = '(' >> lit(":requirements") >> +requirement >> ')';
    auto const constant_def = name;
    auto const variable_def = '?' >> name;
    auto const primitive_type_def = name;
    auto const either_type_def = '(' >> lit("either") >> +primitive_type >> ')';
    auto const type_def = primitive_type | either_type;

    auto const explicitly_typed_list_def = +name >> '-' >> type;

    auto const implicitly_typed_list_def = *name;

    auto const typed_list_def =
        *explicitly_typed_list >> -implicitly_typed_list;

    auto const types_def = '(' >> lit(":types") >> typed_list >> ')';
    auto const domain_def = '(' >> lit("define") >> '(' >> lit("domain") >> name
                            >> ')' >> requirements >> -types >> ')';

    BOOST_SPIRIT_DEFINE(constant,
                        variable,
                        primitive_type,
                        either_type,
                        type,
                        types,
                        predicate,
                        explicitly_typed_list,
                        implicitly_typed_list,
                        typed_list,
                        domain,
                        requirement,
                        requirements);

} // namespace parser

parser::constant_type constant() { return parser::constant; }
parser::variable_type variable() { return parser::variable; }
parser::primitive_type_type primitive_type() { return parser::primitive_type; }
parser::either_type_type either_type() { return parser::either_type; }
parser::type_type type() { return parser::type; }
parser::typed_list_type typed_list() { return parser::typed_list; }
parser::domain_type domain() { return parser::domain; }
parser::requirements_type requirements() { return parser::requirements; }
