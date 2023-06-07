#include <boost/program_options.hpp>
#include <boost/json.hpp>
#include <iostream>
#include <fstream>
#include "cpphop/grapher.h"

namespace json = boost::json;
namespace po = boost::program_options;


int main(int argc, char* argv[]) {
  std::string infile = "";
  std::string outfile = "../data/graph.png";

  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("infile,i", po::value<std::string>(),"json file (string), default = none")
      ("outfile,o", po::value<std::string>(),"png file (string), default = ../data/graph.png")
    ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("infile")) {
      infile = vm["infile"].as<std::string>();
    }

    if (vm.count("outfile")) {
      outfile = vm["outfile"].as<std::string>();
    }

  }
  catch(std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  catch(...) {
    std::cerr << "Exception of unknown type!\n";
  }
  
  if (infile != "") {
    json::value j = parse_file(infile.c_str()); 
    generate_graph_from_json(j.as_object(),j.as_object()["plan"].as_array().size(),j.as_object()["actions"].as_array(),"0",outfile);
  }
  else {
    std::cout << "No json file given." << std::endl;
  }

  return EXIT_SUCCESS;
}
