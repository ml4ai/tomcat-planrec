#pragma once

#include <boost/spirit/home/x3.hpp>

#include "ast.hpp"

namespace parser {
    namespace x3 = boost::spirit::x3;
    using x3::space, x3::lexeme, x3::char_, x3::eol, x3::rule;
    static auto const skipper = space | lexeme[';' >> *(char_ - eol) >> eol];
    // Set up the skip parser so that it can be used from parser.cpp
    using skipper_type = decltype(skipper);
    using phrase_context_type = x3::phrase_parse_context<skipper_type>::type;

    using constant_type = rule<class TConstant, ast::Constant>;
    BOOST_SPIRIT_DECLARE(constant_type);

    using variable_type = rule<class TVariable, ast::Variable>;
    BOOST_SPIRIT_DECLARE(variable_type);

    using primitive_type_type = rule<class TPrimitiveType, ast::PrimitiveType>;
    BOOST_SPIRIT_DECLARE(primitive_type_type);

    using either_type_type = rule<class TEitherType, ast::EitherType>;
    BOOST_SPIRIT_DECLARE(either_type_type);

    using type_type = rule<class TType, ast::Type>;
    BOOST_SPIRIT_DECLARE(type_type);

    // Typed list of names
    using explicitly_typed_list_names_type =
        rule<class TExplicitlyTypedListNames,
             ast::ExplicitlyTypedList<ast::Name>>;
    BOOST_SPIRIT_DECLARE(explicitly_typed_list_names_type);

    using implicitly_typed_list_names_type =
        rule<class TImplicitlyTypedListNames,
             ast::ImplicitlyTypedList<ast::Name>>;
    BOOST_SPIRIT_DECLARE(implicitly_typed_list_names_type);

    using typed_list_names_type =
        rule<class TTypedListNames, ast::TypedList<ast::Name>>;
    BOOST_SPIRIT_DECLARE(typed_list_names_type);

    // Typed list of variables
    using explicitly_typed_list_variables_type =
        rule<class TExplicitlyTypedListVariables,
             ast::ExplicitlyTypedList<ast::Variable>>;
    BOOST_SPIRIT_DECLARE(explicitly_typed_list_variables_type);

    using implicitly_typed_list_variables_type =
        rule<class TImplicitlyTypedListVariables,
             ast::ImplicitlyTypedList<ast::Variable>>;
    BOOST_SPIRIT_DECLARE(implicitly_typed_list_variables_type);

    using typed_list_variables_type =
        rule<class TTypedListVariables, ast::TypedList<ast::Variable>>;
    BOOST_SPIRIT_DECLARE(typed_list_variables_type);

    using requirements_type =
        rule<class TRequirements, std::vector<std::string>>;
    BOOST_SPIRIT_DECLARE(requirements_type);

    using atomic_formula_skeleton_type =
        rule<class TAtomicFormulaSkeleton, ast::AtomicFormulaSkeleton>;
    BOOST_SPIRIT_DECLARE(atomic_formula_skeleton_type);

    using atomic_formula_terms_type =
        rule<class TAtomicFormulaTerms, ast::AtomicFormula<ast::Term>>;
    BOOST_SPIRIT_DECLARE(atomic_formula_terms_type);

    using literal_terms_type =
        rule<class TLiteralTerms, ast::Literal<ast::Term>>;
    BOOST_SPIRIT_DECLARE(literal_terms_type);

    using sentence_type = rule<class TSentence, ast::Sentence>;
    BOOST_SPIRIT_DECLARE(sentence_type);

    using domain_type = rule<class TDomain, ast::Domain>;
    BOOST_SPIRIT_DECLARE(domain_type);

    using problem_type = rule<class TProblem, ast::Problem>;
    BOOST_SPIRIT_DECLARE(problem_type);

    // tag used to get the position cache from the context
    struct position_cache_tag;

} // namespace parser

parser::constant_type constant();
parser::variable_type variable();
parser::primitive_type_type primitive_type();
parser::either_type_type either_type();
parser::type_type type();

parser::explicitly_typed_list_names_type explicitly_typed_list_names();
parser::implicitly_typed_list_names_type implicitly_typed_list_names();
parser::typed_list_names_type typed_list_names();

parser::explicitly_typed_list_variables_type explicitly_typed_list_variables();
parser::implicitly_typed_list_variables_type implicitly_typed_list_variables();
parser::typed_list_variables_type typed_list_variables();

parser::atomic_formula_skeleton_type atomic_formula_skeleton();
parser::atomic_formula_terms_type atomic_formula_terms();
parser::literal_terms_type literal_terms();

parser::sentence_type sentence();
parser::requirements_type requirements();

parser::domain_type domain();
parser::problem_type problem();
