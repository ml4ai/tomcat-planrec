#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>

#include <iostream>
#include <string>

namespace client {
    namespace ast {
        namespace x3 = boost::spirit::x3;

        struct TypedList;

        struct Action {
            std::string name;
            std::vector<std::string> parameters;
        };

        struct Domain {
            std::string name;
            std::vector<std::string> requirements;
            std::vector<std::string> types;
            std::vector<Action> actions;
        };

        //using boost::fusion::operator<<;
    } // namespace ast
} // namespace client

// We need to tell fusion about our domain struct
// to make it a first-class fusion citizen. This has to
// be in global scope.

BOOST_FUSION_ADAPT_STRUCT(client::ast::Action, name, parameters)
BOOST_FUSION_ADAPT_STRUCT(client::ast::Domain, name, requirements, types, actions)

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
        using x3::double_;

        auto const name = lexeme[+(char_ - '(' - ')' - '?')];
        auto const variable = '?' >> name;

        x3::rule<class TAction, ast::Action> const action = "action";
        auto const action_def = 
            '('
            >> lit(":action")
            >> name
            >> '(' >> lit(":parameters") >> +variable >> ')'
            >> ')';

        x3::rule<class TDomain, ast::Domain> const domain = "domain";
        auto const require_def = '(' >> lit(":requirements") >> +name >> ')';
        auto const types_def = '(' >> lit(":types") >> +name >> ')';

        auto const domain_def = 
            '(' 
            >> lit("define") >> '(' >> lit("domain") >> name >> ')' 
            >> -require_def 
            >> -types_def 
            >> +action
            >> ')';

        BOOST_SPIRIT_DEFINE(action, domain);

    } // namespace parser
} // namespace client

void print(client::ast::Domain dom) {
    using namespace std;
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

    cout << "Actions:";
    for (auto x: dom.actions) {
        cout << x.name;
        for (auto p : x.parameters) {
            cout << p;
        }
        cout << endl;
    }
    cout << endl;
}
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

        client::ast::Domain dom;
        iterator_type iter = str.begin();
        iterator_type const end = str.end();
        bool r = phrase_parse(iter, end, domain, space, dom);

        if (r && iter == end) {
            //cout << boost::fusion::tuple_open('[');
            //cout << boost::fusion::tuple_close(']');
            //cout << boost::fusion::tuple_delimiter(", ");

            cout << "-------------------------\n";
            cout << "Parsing succeeded\n";
            print(dom);
            cout << "\n-------------------------\n";
        }
        else {
            cout << "Parsing failed\n";
        }
    }
    return 0;
}
