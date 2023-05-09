#include "util.h"
#include "parsers/map_parser.h"
#include "parsers/map_parser_tools.h"
#include <istream>
#include <boost/program_options.hpp>
#include <fstream>
#include <iomanip>
#include <iostream>
namespace po = boost::program_options;


int main(int argc, char* argv[]) {
  std::string infile = "../apps/data_parsing/Saturn_1.5_3D_sm_v1.0.json";
  std::string outfile = "../apps/data_parsing/Saturn_map_info.json";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("infile,i",po::value<std::string>(),"file to parse (string)")
      ("outfile,o",po::value<std::string>(),"filename for output (string)")
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

  json::value j = parse_file(infile.c_str());

  auto mp = parse_map_from_json(j);

  json::object g;

  g["zones"].emplace_array();
  g["graph"].emplace_object();
  for (auto z : mp.zones) {
    g["zones"].as_array().push_back(json::value_from(z));
    g["graph"].as_object()[z].emplace_array();
    for (auto c : mp.graph[z]) {
      g["graph"].as_object()[z].as_array().push_back(json::value_from(c));
    }
  }
  g["rooms"].emplace_array();
  for (auto r : mp.rooms) {
    g["rooms"].as_array().push_back(json::value_from(r));
  }

  std::ofstream o(outfile);
  o << std::setw(4) << g << std::endl;

  return EXIT_SUCCESS;
}
