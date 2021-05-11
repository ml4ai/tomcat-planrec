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
struct utree_print_2
{
    typedef void result_type;

    std::ostream& out;
    utree_print_2(std::ostream& out) : out(out) {}

    void operator()(utree::invalid_type) const
    {
        out << "<invalid> ";
    }

    void operator()(utree::nil_type) const
    {
        out << "<nil> ";
    }

    template <typename T>
    void operator()(T val) const
    {
        out << val << ' ';
    }

    void operator()(bool b) const
    {
        out << (b ? "true" : "false") << ' ';
    }

    void operator()(binary_range_type const& b) const
    {
        boost::io::ios_all_saver saver(out);
        out << "#";
        out.width(2);
        out.fill('0');

        typedef binary_range_type::const_iterator iterator;
        for (iterator i = b.begin(); i != b.end(); ++i)
            out << std::hex << int((unsigned char)*i);
        out << "# ";
    }

    void operator()(utf8_string_range_type const& str) const
    {
        typedef utf8_string_range_type::const_iterator iterator;
        iterator i = str.begin();
        out << '"';
        for (; i != str.end(); ++i)
            out << *i;
        out << "\" ";
    }

    void operator()(utf8_symbol_range_type const& str) const
    {
        typedef utf8_symbol_range_type::const_iterator iterator;
        iterator i = str.begin();
        for (; i != str.end(); ++i)
            out << *i;
        out << ' ';
    }

    template <typename Iterator>
    void operator()(boost::iterator_range<Iterator> const& range) const
    {
        typedef typename boost::iterator_range<Iterator>::const_iterator iterator;
        (*this)('(');
        for (iterator i = range.begin(); i != range.end(); ++i)
        {
            boost::spirit::utree::visit(*i, *this);
        }
        (*this)(')');
    }

    void operator()(any_ptr const&) const
    {
        return (*this)("<pointer>");
    }

    void operator()(function_base const&) const
    {
        return (*this)("<function>");
    }
};
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
            auto print = boost::spirit::utree_print_2(std::cout);
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
