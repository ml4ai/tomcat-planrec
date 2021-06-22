#pragma once

#include <boost/spirit/home/x3.hpp>

#include "ast.hpp"

namespace client {
    ///////////////////////////////////////////////////////////////////////////////
    //  Our domain parser declaration
    ///////////////////////////////////////////////////////////////////////////////
    namespace parser {
        namespace x3 = boost::spirit::x3;
        using x3::space, x3::lexeme, x3::char_, x3::eol;
        static auto const skipper = space | lexeme[';' >> *(char_ - eol) >> eol];
        // Set up the skip parser so that it can be used from parser.cpp
        using skipper_type=decltype(skipper);
        using phrase_context_type = x3::phrase_parse_context<skipper_type>::type;
        using domain_type = x3::rule<class TDomain, ast::Domain>;
        using problem_type = x3::rule<class TProblem, ast::Problem>;

        BOOST_SPIRIT_DECLARE(domain_type);
        BOOST_SPIRIT_DECLARE(problem_type);

        // tag used to get the position cache from the context
        struct position_cache_tag;

    } // namespace parser

    parser::domain_type domain();
    parser::problem_type problem();
} // namespace client
