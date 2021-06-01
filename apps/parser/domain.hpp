#pragma once

#include <boost/config/warning_disable.hpp>
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
        using domain_type = x3::rule<class TDomain, ast::Domain>;
        BOOST_SPIRIT_DECLARE(domain_type);
    } // namespace parser

    parser::domain_type domain();
} // namespace client
