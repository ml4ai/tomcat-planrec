#include <fstream>
#include <iostream>
#include <string>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "domain.hpp"
#include "error_handler.hpp"
#include "config.hpp"

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
    using client::domain;

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
        cerr << "Error: Could not open input file: " << filename << endl;
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

    using boost::spirit::x3::with;
    using client::parser::error_handler_type;

    error_handler_type error_handler(iter, end, std::cerr);

    auto const parser = with<client::parser::error_handler_tag>(std::ref(error_handler)) [
        domain()
    ];

    bool r = phrase_parse(iter, end, parser, client::parser::skipper, dom);

    if (r && iter == end) {
        std::cout << "-------------------------\n";
        std::cout << "Parsing succeeded\n";
        std::cout << "-------------------------\n";
        print(dom);
        return 0;
    }
    else {
        std::cout << "-------------------------\n";
        std::cout << "Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error! Expecting end of input here: ");
        return 1;
    }
    return 0;
}
