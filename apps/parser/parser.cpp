#include <boost/config/warning_disable.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>

#include <iostream>
#include <string>

namespace client {
    namespace ast {
        struct domain {
            std::string name;
            std::vector<std::string> requirements;
            std::vector<std::string> types;
        };

        //using boost::fusion::operator<<;
    } // namespace ast
} // namespace client

// We need to tell fusion about our domain struct
// to make it a first-class fusion citizen. This has to
// be in global scope.

BOOST_FUSION_ADAPT_STRUCT(client::ast::domain, name, requirements, types)

namespace client {
    ///////////////////////////////////////////////////////////////////////////////
    //  Our domain parser
    ///////////////////////////////////////////////////////////////////////////////
    namespace parser {
        namespace x3 = boost::spirit::x3;
        namespace ascii = boost::spirit::x3::ascii;

        using ascii::char_;
        using x3::lexeme;
        using x3::lit;

        x3::rule<class domain, ast::domain> const domain = "domain";

        auto const name = lexeme[+(char_ - ')')];
        auto const variable = '?' >> name;
        auto const require_def = '(' >> lit(":requirements") >> +name >> ')';
        auto const types_def = '(' >> lit(":types") >> +name >> ')';
        auto const domain_def = '(' >> lit("define") >> '(' >> lit("domain") >> name >> ')' >>
            -require_def >> -types_def >> ')';

        BOOST_SPIRIT_DEFINE(domain);
    } // namespace parser
} // namespace client

////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////
int main() {
    using namespace std;
    using boost::spirit::x3::ascii::space;
    typedef string::const_iterator iterator_type;
    using client::parser::domain;

    string str;
    while (getline(cin, str)) {
        if (str.empty() || str[0] == 'q' || str[0] == 'Q')
            break;

        client::ast::domain dom;
        iterator_type iter = str.begin();
        iterator_type const end = str.end();
        bool r = phrase_parse(iter, end, domain, space, dom);

        if (r && iter == end) {
            //cout << boost::fusion::tuple_open('[');
            //cout << boost::fusion::tuple_close(']');
            //cout << boost::fusion::tuple_delimiter(", ");

            cout << "-------------------------\n";
            cout << "Parsing succeeded\n";
            cout << "Name: " << dom.name << endl;
            cout << "Requirements: ";
            for (auto x: dom.requirements) {
                cout << x;
            }
            cout << endl;
            cout << "Types: ";
            for (auto x: dom.types) {
                cout << x;
            }
            cout << endl;
            cout << "\n-------------------------\n";
        }
        else {
            cout << "Parsing failed\n";
        }
    }
    return 0;
}
