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

  std::ifstream i(infile);
  json j;
  i >> j; 

  std::vector<std::string> alt_zones = {"sga","ew","cf","kit","lib","llc","sdc","loc_42"};

  auto mp = parse_map_from_json(j, alt_zones);

  json g;

  mp.zones.push_back("UNKNOWN");

  mp.graph["llcn"].push_back("UNKNOWN");

  mp.graph["UNKNOWN"].push_back("llcn");

  mp.graph["r103"].push_back("UNKNOWN");

  mp.graph["UNKNOWN"].push_back("r103");

  for (auto z : mp.zones) {
    g["zones"].push_back(z);
    for (auto c : mp.graph[z]) {
      g["graph"][z].push_back(c);
    }
    g["dist_from_change_zone"][z] = shortest_path_BFS(mp.graph,z,"sga");
  }

  for (auto r : mp.rooms) {
    g["rooms"].push_back(r);
  }

  g["change_zone"] = "sga";

  g["no_victim_zones"].push_back("sga");

  g["multi_room_zones"].push_back("cf");

  g["multi_room_zones"].push_back("kit");

  g["multi_room_zones"].push_back("lib");

  g["multi_room_zones"].push_back("llc");

  g["multi_room_zones"].push_back("sdc");

  std::ofstream o(outfile);
  o << std::setw(4) << g << std::endl;

  return EXIT_SUCCESS;
}
