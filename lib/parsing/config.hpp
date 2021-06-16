#pragma once

#include "error_handler.hpp"
#include <boost/spirit/home/x3.hpp>

namespace client {
    namespace parser {
        namespace x3 = boost::spirit::x3;

        using x3::error_handler_tag;

        using iterator_type = std::string::const_iterator;
        // Our Error Handler
        using error_handler_type = boost::spirit::x3::error_handler<iterator_type>;

        // Combined Error Handler and Phrase Parse Context
        typedef x3::context<x3::error_handler_tag,
                            std::reference_wrapper<error_handler_type>,
                            phrase_context_type>
            context_type;
    } // namespace parser
} // namespace client
