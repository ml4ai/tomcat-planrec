#include <nlohmann/json.hpp>
#include "../data_parsing/parsers/team_comp_sar_parser.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include "cppCFMtrain.h"
#include <boost/program_options.hpp>
namespace po = boost::program_options;

using json = nlohmann::json;

using namespace std;

int main(int argc, char* argv[]) {
  std::string infile = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-4.metadata";
  std::string map_json = "../apps/data_parsing/Saturn_map_info.json";
  std::string outfile = "team_comp_cfm.json";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("file,f",po::value<std::string>(),"file to parse (string)")
      ("map_json,m", po::value<std::string>(),"json file with map data (string)")
      ("outfile,o",po::value<std::string>(),"json file to output (string)")
    ;

    po::variables_map vm;        
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("file")) {
      infile = vm["file"].as<std::string>();
    }

    if (vm.count("map_json")) {
      map_json = vm["map_json"].as<std::string>();
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
 

    std::ifstream f(map_json);
    json g;
    f >> g;

    auto state1 = TeamSARState();
    
    state1.class_only_boundary = "el";
    state1.change_zone = g["change_zone"].get<std::string>();
    for (auto& nvz : g["no_victim_zones"]) {
      state1.no_victim_zones.push_back(nvz.get<std::string>());
    }
    for (auto& mrz : g["multi_room_zones"]) {
      state1.multi_room_zones.push_back(mrz.get<std::string>());
    }
    for (auto& z : g["zones"]) {
      state1.zones.push_back(z.get<std::string>());
    }

    for (auto& [l,vl] : g["graph"].items()) {
      for (auto& c : vl) {
        state1.graph[l].push_back(c.get<std::string>());
      }
    }

    for (auto& [d,di] : g["dist_from_change_zone"].items()) {
        state1.dist_from_change_zone[d] = di.get<int>();
    }

    for (auto& mrz : g["multi_room_zones"]) {
      state1.multi_room_zones.push_back(mrz.get<std::string>());
    }
    for (auto& r : g["rooms"]) {
      state1.rooms.push_back(r.get<std::string>());
    }
    
    for (auto s : state1.zones) {
      state1.blocks_broken[s] = 0;

      state1.r_triaged_here[s] = false;

      state1.c_triaged_here[s] = false;

      state1.c_awake[s] = false;

    }

    state1.c_triage_total = 0;
  
    state1.r_triage_total = 0;
  
    state1.c_max = 5;
    state1.r_max = 50;
  
    auto domain = TeamSARDomain();

    parse_data p;

    p = team_sar_parser(infile,state1, domain, -1);

    p.initial_state.action_tracker = p.action_tracker;
    p.initial_state.loc_tracker = p.loc_tracker;

    Tasks tasks = {
      {Task("SAR", Args({{"agent3", p.initial_state.agents[2]},
                         {"agent2", p.initial_state.agents[1]},
                         {"agent1", p.initial_state.agents[0]}}),{"agent1","agent2","agent3"},{p.initial_state.agents[0],p.initial_state.agents[1],p.initial_state.agents[2]})}};
    auto cfms = cppCFMtrain(p.team_plan,
                          p.initial_state,
                          tasks,
                          domain);
    std::cout << "Training Complete, summing CFMs" << std::endl;
    auto cfm = sumCFMs(cfms);
    std::cout << "Summing Complete, saving CFM to json" << std::endl;
    json jcfm = cfm;
    std::ofstream o(outfile);
    o << std::setw(4) << jcfm << std::endl;
    return EXIT_SUCCESS;
}
