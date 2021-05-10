/*==============================================================================
    Copyright (c) 2001-2011 Hartmut Kaiser
    Copyright (c) 2001-2011 Joel de Guzman
    Copyright (c) 2010-2011 Bryce Lelbach

    Distributed under the Boost Software License, Version 1.0. (See accompanying
    file BOOST_LICENSE_1_0.rst or copy at http://www.boost.org/LICENSE_1_0.txt)
==============================================================================*/

#include <boost/spirit/include/qi_parse.hpp>
#include <boost/spirit/include/support_istream_iterator.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/spirit/home/support/utree.hpp>

#include "sexpr_parser.hpp"

int main() {
    using boost::spirit::qi::phrase_parse;

    std::cout << "sexpr parser...\n\n";
    std::cout << "Type an expression... or [q or Q] to quit\n\n";

    typedef std::string::const_iterator iterator_type;
    typedef sexpr::parser<iterator_type> parser;
    typedef sexpr::whitespace<iterator_type> space;

    parser p;
    space ws;
    boost::spirit::utree ut;

    std::string str;
    while (std::getline(std::cin, str)) {
        if (str.empty() || str[0] == 'q' || str[0] == 'Q')
            break;

        std::string::const_iterator iter = str.begin();
        std::string::const_iterator end = str.end();
        bool r = phrase_parse(iter, end, p, ws, ut);

        if (r && iter == end) {
            std::cout << "-------------------------\n";
            std::cout << "Parsing succeeded\n";
            std::cout << "-------------------------\n";
            auto print = boost::spirit::utree_print(std::cout);
            for ( auto x : ut ) { std::cout << x << ":" << x.which() << std::endl; }
        }
        else {
            std::string rest(iter, end);
            std::cout << "-------------------------\n";
            std::cout << "Parsing failed\n";
            std::cout << "stopped at: \": " << rest << "\"\n";
            std::cout << "-------------------------\n";
        }
    }

    std::cout << "Bye... :-) \n\n";
    return 0;
}
