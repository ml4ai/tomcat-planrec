#pragma once

#include <boost/spirit/home/x3.hpp>

#include "ast.hpp"

namespace parser {
    namespace x3 = boost::spirit::x3;
    using x3::space, x3::lexeme, x3::char_, x3::eol, x3::rule;
    static auto const skipper = space | lexeme[';' >> *(char_ - eol) >> eol];
    // Set up the skip parser so that it can be used from parser.cpp
    using skipper_type=decltype(skipper);
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

    using explicitly_typed_list_type = rule<class TExplicitlyTypedList, ast::ExplicitlyTypedList>;
    BOOST_SPIRIT_DECLARE(explicitly_typed_list_type);

    using implicitly_typed_list_type = rule<class TImplicitlyTypedList, ast::ImplicitlyTypedList>;
    BOOST_SPIRIT_DECLARE(implicitly_typed_list_type);

    using typed_list_type = rule<class TTypedList, ast::TypedList>;
    BOOST_SPIRIT_DECLARE(typed_list_type);


    // tag used to get the position cache from the context
    struct position_cache_tag;

} // namespace parser

parser::constant_type constant();
parser::variable_type variable();
parser::primitive_type_type primitive_type();
parser::either_type_type either_type();
parser::type_type type();
parser::explicitly_typed_list_type explicitly_typed_list();
parser::implicitly_typed_list_type implicitly_typed_list();
parser::typed_list_type typed_list();
