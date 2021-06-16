#define BOOST_TEST_MODULE TestParser

#include <boost/test/included/unit_test.hpp>

#include <fstream>
#include <iostream>
#include <string>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "config.hpp"
#include "domain.hpp"
#include "error_handler.hpp"
#include <boost/program_options.hpp>

#include <iostream>
#include <algorithm>
#include <iterator>
#include <unistd.h> // to sleep: sleep(1);

using namespace boost;
namespace po = boost::program_options;
using namespace std;
using boost::unit_test::framework::master_test_suite;


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




// A helper function to simplify the main part.
template<class T>
ostream& operator<<(ostream& os, const vector<T>& v)
{
    copy(v.begin(), v.end(), ostream_iterator<T>(os, " "));
    return os;
}

int main(int argc, char* argv[])  {

  // defiing filename before the programming options, and as a string:
  string filename;
  
/********************  part of the programs options*/
    try {
        int opt, portnum;// not for domain. 
        string domain_choice, problem_choice;

        po::options_description desc("Allowed options");
        desc.add_options()
            ("help,h", "Show help message")
            ("domain,d", po::value<string>(&domain_choice)->default_value("../test.pddl"), 
             "Choice of Domain")
              ("problem,p", po::value<string>()->default_value("../problem.pddl"), "Choice of Problem")

            ("optimization", po::value<int>(&opt)->default_value(10),
                  "optimization level")
            ("verbose,v", po::value<int>()->implicit_value(1),
                  "enable verbosity (optionally specify level)")
            ("listen,l", po::value<int>(&portnum)->implicit_value(1001)
                  ->default_value(0,"no"),
                  "listen on a port.")
            ("include-path,I", po::value< vector<string> >(),
                  "include path")
            ("input-file", po::value< vector<string> >(), "input file")
        ;

        po::positional_options_description p;
        p.add("problem", -1);
        p.add("domain", -1);

        po::variables_map vm;
        po::store(po::command_line_parser(argc, argv).
                  options(desc).positional(p).run(), vm);
        //always notify after I store command-line options:
        po::notify(vm);

        if (vm.count("help")) {
            cout << "Usage: options_description [options]\n";
            cout << desc;
            return 0;
        }

//Trying problem program option:
        if (vm.count("domain"))
        {
            cout << "Chosen domain is: "
                 << vm["domain"].as< string>() << "\n";
        }

        if (vm.count("problem"))
        {
            cout << "Chosen Problem is: "
                 << vm["problem"].as< string>() << "\n";
            filename = vm["problem"].as<string>(); 
        }


        if (vm.count("include-path"))
        {
            cout << "Include paths are: "
                 << vm["include-path"].as< vector<string> >() << "\n";
        }

        if (vm.count("input-file"))
        {
            cout << "Input files are: "
                 << vm["input-file"].as< vector<string> >() << "\n";
        }

        if (vm.count("verbose")) {
            cout << "Verbosity enabled.  Level is " << vm["verbose"].as<int>()
                 << "\n";
        }

        //These are irrelevant for the domain:
        //cout << "Example po: Optimization level is " << opt << "\n";
        //cout << "Example po: Listen port is " << portnum << "\n";
        
        cout << "End of program options trial.\n\n";

    }
    catch(std::exception& e) {
        cout << e.what() << "\n";
        return 1;
    }

/******************** end of programs options **************************/

/******************** start of parser.cpp for tomcat *******************/

    using namespace std;
    typedef string::const_iterator iterator_type;
    using client::domain;
    using client::problem;


/* I took out the char const* filename definition here so it is no longer
 * defined without program options. Before, the program options object value
 * would be overwritten and fail due to the else clause. This is commented out
 * so I can commit why I made these changes. Next commit will not have these
 * next few lines:
 *
 * Trying to get 2nd part to talk to 3rd part!!!
    if (argc > 1) {
        filename = argv[1];
    }
    else {
        std::cerr << "Error: No input file provided." << std::endl;
        return 1;
    }
*/
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

    std::cout << "---------------------------------------\n";
    std::cout << "Now parsing domain:\n";
    sleep(2);

    if (!(r && iter == end)) {
        std::cout << "-------------------------\n";
        std::cout << "Domain Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
    }    

    data.print(dom);

    auto const pParser =
        with<error_handler_tag>(std::ref(error_handler))[problem()];

    std::cout << "---------------------------------------\n";
    cout << "Now parsing problem:\n";
    sleep(2);

    bool s = phrase_parse(iter, end, pParser, client::parser::skipper, prob);

    if (!(s && iter == end)) {
        std::cout << "-------------------------\n";
        std::cout << "Problem Parsing failed\n";
        std::cout << "-------------------------\n";
        error_handler(iter, "Error!");
    }

    data.print(prob);
/******************** end of parser.cpp for tomcat *******************/
  
    BOOST_TEST(dom.name == "construction"); 

    return 0;
}//end main()
