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
    rule<class TTypes, TypedList<Name>> const types = "types";
    rule<class Predicate, Name> const predicate = "predicate";
    rule<class TRequirements, std::vector<Name>> const requirements =
        "requirements";
    rule<class TRequirement, std::vector<Name>> const requirement =
        "requirement";

    auto const requirement_def = ':' >> name;
    auto const predicate_def = name;
    auto const requirements_def = '(' >> lit(":requirements") >> +requirement >>
                                  ')';
    auto const constant_def = name;
    auto const variable_def = '?' >> name;
    auto const primitive_type_def = name;
    auto const either_type_def = '(' >> lit("either") >> +primitive_type >> ')';
    auto const type_def = primitive_type | either_type;

    // Typed list of names
    rule<class TExplicitlyTypedListNames, ExplicitlyTypedList<Name>> const
        explicitly_typed_list_names = "explicitly_typed_list_names";
    rule<class TImplicitlyTypedListNames, ImplicitlyTypedList<Name>> const
        implicitly_typed_list_names = "implicitly_typed_list_names";
    rule<class TTypedListNames, TypedList<Name>> const typed_list_names =
        "typed_list_names";
    auto const explicitly_typed_list_names_def = +name >> '-' >> type;
    auto const implicitly_typed_list_names_def = *name;
    auto const typed_list_names_def =
        *explicitly_typed_list_names >> -implicitly_typed_list_names;
    BOOST_SPIRIT_DEFINE(explicitly_typed_list_names,
                        implicitly_typed_list_names,
                        typed_list_names);

    // Typed list of variables
    rule<class TExplicitlyTypedListVariables, ExplicitlyTypedList<Variable>> const
        explicitly_typed_list_variables = "explicitly_typed_list_variables";
    rule<class TImplicitlyTypedListVariables, ImplicitlyTypedList<Variable>> const
        implicitly_typed_list_variables = "implicitly_typed_list_variables";
    rule<class TTypedListVariables, TypedList<Variable>> const typed_list_variables =
        "typed_list_variables";
    auto const explicitly_typed_list_variables_def = +variable >> '-' >> type;
    auto const implicitly_typed_list_variables_def = *variable;
    auto const typed_list_variables_def =
        *explicitly_typed_list_variables >> -implicitly_typed_list_variables;
    BOOST_SPIRIT_DEFINE(explicitly_typed_list_variables,
                        implicitly_typed_list_variables,
                        typed_list_variables);

    // Atomic formula skeleton
    rule<class TAtomicFormulaSkeleton, ast::AtomicFormulaSkeleton> const atomic_formula_skeleton = "atomic_formula_skeleton";
    auto const atomic_formula_skeleton_def = '(' >> name >> typed_list_variables >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_skeleton);

    auto const types_def = '(' >> lit(":types") >> typed_list_names >> ')';

    rule<class TConstants, TypedList<Name>> const constants = "constants";
    auto const constants_def = '(' >> lit(":constants") >> typed_list_names >> ')';
    BOOST_SPIRIT_DEFINE(constants);

    rule<class TPredicates, std::vector<ast::AtomicFormulaSkeleton>> const predicates = "predicates";
    auto const predicates_def = '(' >> lit(":predicates") >> +atomic_formula_skeleton >> ')';
    BOOST_SPIRIT_DEFINE(predicates);

    rule<class TDomain, ast::Domain> const domain = "domain";
    auto const domain_def = '(' >> lit("define") >> '(' >> lit("domain") >> name
                            >> ')' >> requirements >> -types >> -constants >> -predicates >> ')';
    BOOST_SPIRIT_DEFINE(domain);

    rule<class TObjects, TypedList<Name>> const objects = "objects";
    auto const objects_def = '(' >> lit(":objects") >> typed_list_names >> ')';
    BOOST_SPIRIT_DEFINE(objects);

    rule<class TProblem, ast::Problem> const problem = "problem";
    auto const problem_def = '(' >> lit("define") >> '(' >> lit("problem") >> name >> ')'
        >> '(' >> lit(":domain") >> name >> ')' >> -requirements >> -objects >> ')';
    BOOST_SPIRIT_DEFINE(problem);

    BOOST_SPIRIT_DEFINE(constant,
                        variable,
                        primitive_type,
                        either_type,
                        type,
                        types,
                        predicate,
                        requirement,
                        requirements);

} // namespace parser

parser::constant_type constant() { return parser::constant; }
parser::variable_type variable() { return parser::variable; }
parser::primitive_type_type primitive_type() { return parser::primitive_type; }
parser::either_type_type either_type() { return parser::either_type; }
parser::type_type type() { return parser::type; }
parser::typed_list_names_type typed_list_names() {
    return parser::typed_list_names;
}
parser::typed_list_variables_type typed_list_variables() {
    return parser::typed_list_variables;
}
parser::atomic_formula_skeleton_type atomic_formula_skeleton() { return parser::atomic_formula_skeleton; }
parser::requirements_type requirements() { return parser::requirements; }
parser::domain_type domain() { return parser::domain; }
parser::problem_type problem() { return parser::problem; }
