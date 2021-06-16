#include <fstream>
#include <iostream>
#include <string>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "config.hpp"
#include "domain.hpp"
#include "error_handler.hpp"

// Print Domain or Problem Parsing:
class Print{

  public:
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
        cout << "  " << x << endl;
    }
    cout << endl;

    cout << "Actions:" << endl;
    for (auto x : dom.actions) {
        cout << x.name << endl;
        cout << "  parameters: " << endl;
        for (auto p : x.parameters) {
            cout << "  " << p << endl;
        }
        cout << endl;
        cout << "  precondition: " << endl;
        for (auto lit : x.precondition) {
            cout << "  (" << lit.predicate << " ";
            for (auto arg : lit.args) {
                cout << arg.name << " ";
            }
            cout << ')' << endl;
        }
        cout << endl; // Line between each action parsed
    }
    cout << endl;

    cout << "Constants:" << endl;
    for (auto constant : dom.constants) {
        cout << "  " << constant  << endl;;
    }
    cout << endl;

    cout << "Predicates:" << endl;
    for (auto x : dom.predicates) {
        cout << "  " << x.predicate;
        for (auto variable : x.variables) {
            cout << " " << variable;
        }
        cout << endl;
    }
    cout << endl;
  }// end print()

    void print(client::ast::Problem prob) {
        using namespace std;
        cout << "Problem Name: " << prob.name << endl;
        cout << "Problem Domain: " << prob.probDomain << endl;
        cout << "Requirements: " << endl;
        for (auto x : prob.requireDomain) {
            cout << '"' << x << '"' << endl;
        }
        cout << endl;
        cout << "Objects: " << endl;
        for (auto x : prob.objects) {
            cout << "  " << x << endl;
        }
        cout << endl;
  }//end print()
};// end Print class


////////////////////////////////////////////////////////////////////////////
//  Main program
////////////////////////////////////////////////////////////////////////////

int main(int argc, char* argv[]) {

    using namespace std;
    typedef string::const_iterator iterator_type;
    using client::domain;
    using client::problem;

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
    client::ast::Problem prob;

    using boost::spirit::x3::with;
    using client::parser::error_handler_tag;
    using client::parser::error_handler_type;

    error_handler_type error_handler(iter, end, std::cerr);

    // Overloading print()
    Print data;

    auto const parser =
        with<error_handler_tag>(std::ref(error_handler))[domain()];

    bool r = phrase_parse(iter, end, parser, client::parser::skipper, dom);

    if (r && iter == end) {
        std::cout << "-------------------------\n";
        std::cout << "Domain Parsing succeeded\n";
        std::cout << "-------------------------\n";
        data.print(dom);
    }
    else {
        std::cout << "-------------------------\n";
        std::cout << "Domain Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
// Commented out return 1 for now until I create program options to
   // separate problem and domain parsing
        //return 1;

    }

    auto const pParser =
        with<error_handler_tag>(std::ref(error_handler))[problem()];

    bool s = phrase_parse(iter, end, pParser, client::parser::skipper, prob);

    if (s && iter == end) {
        std::cout << "-------------------------\n";
        std::cout << "Problem Parsing succeeded\n";
        std::cout << "-------------------------\n";
        data.print(prob);
    }
    else {
        std::cout << "-------------------------\n";
        std::cout << "Problem Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
        return 1;
    }

    return 0;
}
