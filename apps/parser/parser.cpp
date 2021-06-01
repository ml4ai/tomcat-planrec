#include <boost/config/warning_disable.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/fusion/include/deque.hpp>
#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>

#include <iostream>
#include <string>
#include <fstream>

namespace client {
    namespace ast {
        namespace x3 = boost::spirit::x3;

        using name = std::string;

        struct Entity {
            std::string name;
            std::string type;
            Entity(const std::string name, const std::string type = "object")
                : name(name), type(type){};
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

        // using boost::fusion::operator<<;
    } // namespace ast
} // namespace client

// We need to tell fusion about our domain structs to make them first-class
// fusion citizens. This has to be in global scope.

BOOST_FUSION_ADAPT_STRUCT(client::ast::Entity, name, type)
BOOST_FUSION_ADAPT_STRUCT(client::ast::Action, name, parameters)
BOOST_FUSION_ADAPT_STRUCT(
    client::ast::Domain, name, requirements, types, actions)

namespace client {
    ///////////////////////////////////////////////////////////////////////////////
    //  Our domain parser
    ///////////////////////////////////////////////////////////////////////////////
    namespace parser {
        namespace x3 = boost::spirit::x3;

        using boost::fusion::at_c;
        using client::ast::Entity;
        using x3::ascii::char_, x3::lexeme, x3::lit, x3::alnum, x3::_attr,
            x3::_val, x3::space, x3::eol;

        auto const name = lexeme[+(char_ - '?' - '(' - ')' - ':' - space)];
        auto const requirement = ':' >> name;
        auto const variable = '?' >> name;
        auto const require_def =
            '('
            >> lit(":requirements")
            >> +requirement
            >> ')';
        auto const types_def = '(' >> lit(":types") >> +name >> ')';

        x3::rule<class TTypedList, ast::TypedList> const typed_list =
            "typed_list";

        auto add_implicitly_typed_entity = [](auto& ctx) {
            _val(ctx).push_back(Entity(_attr(ctx)));
        };

        auto add_explicitly_typed_entities = [](auto& ctx) {
            auto dq = _attr(ctx);
            std::vector<std::string> names = at_c<0>(dq);
            std::string type = at_c<1>(dq);

            for (std::string& name : names) {
                Entity entity = Entity(name, type);
                _val(ctx).push_back(entity);
            }
        };

        auto const implicitly_typed_list =
            *variable[add_implicitly_typed_entity];
        auto const explicitly_typed_list =
            (+variable >> '-' >> name)[add_explicitly_typed_entities];
        auto const typed_list_def =
            *explicitly_typed_list >> -implicitly_typed_list;

        x3::rule<class TAction, ast::Action> const action = "action";
        auto const action_def = '(' >> lit(":action") >> name >>
                                lit(":parameters") >> '(' >> typed_list
                                >> ')' >> ')';

        x3::rule<class TDomain, ast::Domain> const domain = "domain";
        auto const domain_def = '(' >> lit("define") >> '(' >>
                                lit("domain") >> name >> ')' >> -require_def >>
                                -types_def >> +action >> ')';

        BOOST_SPIRIT_DEFINE(typed_list, action, domain);

        auto const skipper = space | lexeme[';' >> *(char_ - eol) >> eol];

    } // namespace parser
} // namespace client

void print(client::ast::Domain dom) {
    using namespace std;
    cout << "Name: " << dom.name << endl;
    cout << "Requirements: " << endl;
    for (auto x : dom.requirements) {
        cout << '"' << x << '"' << endl;
    }
    cout << endl;
    cout << "Types: " << endl;
    for (auto x : dom.types) {
        cout << x;
    }
    cout << endl;

    cout << "Actions:" << endl;
    for (auto x : dom.actions) {
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
int main(int argc, char* argv[]) {
    using namespace std;
    typedef string::const_iterator iterator_type;
    using client::parser::domain;

    char const* filename;
    if (argc > 1) {
        filename = argv[1];
    }
    else {
        std::cerr << "Error: No input file provided." << std::endl;
        return 1;
    }

    ifstream in(filename, ios_base::in);

    if (!in) {
        cerr << "Error: Could not open input file: " << filename
                  << endl;
        return 1;
    }

    string storage;         // We will read the contents here.
    in.unsetf(ios::skipws); // No white space skipping!
    copy(istream_iterator<char>(in),
              istream_iterator<char>(),
              back_inserter(storage));


    string::const_iterator iter = storage.begin();
    string::const_iterator end = storage.end();
    client::ast::Domain dom;
    bool r = phrase_parse(iter, end, domain, client::parser::skipper, dom);

    if (r && iter == end)
    {
        std::cout << "-------------------------\n";
        std::cout << "Parsing succeeded\n";
        std::cout << "-------------------------\n";
        print(dom);
        return 0;
    }
    else
    {
        std::cout << "-------------------------\n";
        std::cout << "Parsing failed\n";
        std::cout << "-------------------------\n";
        return 1;
    }
    return 0;
}
