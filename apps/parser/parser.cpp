#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include <boost/fusion/include/deque.hpp>

#include <iostream>
#include <string>

namespace client {
    namespace ast {
        namespace x3 = boost::spirit::x3;

        using name = std::string;

        struct Entity {
            std::string name;
            std::string type;
            Entity(const std::string name, const std::string type = "object") : name(name), type(type) {};
        };

        using TypedList = std::vector<Entity>;

        struct Action {
            std::string name;
            TypedList parameters;
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

BOOST_FUSION_ADAPT_STRUCT(client::ast::Entity, name, type)
//BOOST_FUSION_ADAPT_STRUCT(client::ast::TypedList)
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
        using x3::_attr;
        using boost::fusion::at_c;

        auto const name = lexeme[+x3::alnum];
        auto const requirement = ':' >> name;
        auto const variable = '?' >> name;
        auto const require_def = '(' >> lit(":requirements") >> +requirement >> ')';
        auto const types_def = '(' >> lit(":types") >> +name >> ')';


        x3::rule<class TTypedList, ast::TypedList> const typed_list = "typed_list";

        auto pb = [](auto& ctx){
            x3::_val(ctx).push_back(ast::Entity(x3::_attr(ctx)));
        };

        auto pb2 = [](auto& ctx){
            for (auto x : at_c<0>(_attr(ctx))) {
                x3::_val(ctx).push_back(ast::Entity(x, at_c<1>(_attr(ctx))));
            }
        };

        auto const typed_list_def =
            (+name >> '-' >> name)[pb2] | 
            *name[pb]
            ;

        x3::rule<class TAction, ast::Action> const action = "action";
        auto const action_def = 
            '('
            >> lit(":action")
            >> name
            >> '(' >> lit(":parameters") >> typed_list >> ')'
            >> ')';

        x3::rule<class TDomain, ast::Domain> const domain = "domain";
        auto const domain_def = 
            '(' 
            >> lit("define") >> '(' >> lit("domain") >> name >> ')' 
            >> -require_def 
            >> -types_def 
            >> +action
            >> ')';

        BOOST_SPIRIT_DEFINE(typed_list, action, domain);

    } // namespace parser
} // namespace client

void print(client::ast::Domain dom) {
    using namespace std;
    cout << "Name: " << dom.name << endl;
    cout << "Requirements: " << endl;
    for (auto x: dom.requirements) {
        cout << '"' << x  << '"' << endl;
    }
    cout << endl;
    cout << "Types: " << endl;
    for (auto x: dom.types) {
        cout << x;
    }
    cout << endl;

    cout << "Actions:" << endl;
    for (auto x: dom.actions) {
        cout << x.name << endl;
        cout << "parameters: " << endl;
        for (auto p : x.parameters) {
            cout << "parameter name: " << p.name << endl;
            cout << "type: " << p.type << endl;
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
