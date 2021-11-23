#include <nlohmann/json.hpp>
#include "../data_parsing/parsers/team_comp_sar_parser.h"
#include <math.h>
#include <stdlib.h>
#include <iostream>
#include "cppMCTStrain.h"
#include <boost/program_options.hpp>
namespace po = boost::program_options;

using json = nlohmann::json;

using namespace std;

int main(int argc, char* argv[]) {
  bool use_t = false; 
  int R = 30;
  double e = 0.4;
  int aux_R = 10;

  std::string infile1 = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000415_Team-TM000108_Member-na_CondBtwn-1_CondWin-SaturnA_Vers-4.metadata";
  std::string infile2 = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-4.metadata";
  std::string map_json = "../apps/data_parsing/Saturn_map_info.json";
  std::string cpm_json;
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int)")
      ("exp_param,e",po::value<double>(),"The exploration parameter for the plan recognition algorithm (double)")
      ("map_json,m", po::value<std::string>(),"json file with map data (string)")
      ("cpm_json,j",po::value<std::string>(),"json file to parse CPM (string)")
      ("aux_r,a", po::value<int>(), "Auxiliary resources for bad expansions (int)")
    ;

    po::variables_map vm;        
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("resource_cycles")) {
      R = vm["resource_cycles"].as<int>();
    }

    if (vm.count("exp_param")) {
      e = vm["exp_param"].as<double>();
    }

    if (vm.count("aux_r")) {
      aux_R = vm["aux_r"].as<int>();
    }

    if (vm.count("cpm_json")) {
      cpm_json = vm["cpm_json"].as<std::string>();
    }

    if (vm.count("map_json")) {
      map_json = vm["map_json"].as<std::string>();
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

    CPM cpm = {};

    if (cpm_json != "") {
      std::ifstream i(cpm_json);
      json j;
      i >> j;
      for (auto& [k1, v1] : j.items()) {
        for (auto& [k2,v2] : v1.items()) {
          for (auto& [k3,v3] : v2.items()) {
            cpm[k1][k2][k3] = v3;
          }
        }
      }
    }

    parse_data p1;

    p1 = team_sar_parser(infile1,state1, domain, -1);

    
    p1.initial_state.action_tracker = p1.action_tracker;
    p1.initial_state.loc_tracker = p1.loc_tracker;

    p1.initial_state.plan_rec = true;

    Tasks tasks1 = {
      {Task("SAR", Args({{"agent3", p1.initial_state.agents[2]},
                         {"agent2", p1.initial_state.agents[1]},
                         {"agent1", p1.initial_state.agents[0]}}),{"agent1","agent2","agent3"},{p1.initial_state.agents[0],p1.initial_state.agents[1],p1.initial_state.agents[2]})}};

    auto cfm1 = cppMCTStrain(p1.team_plan,
                          p1.initial_state,
                          tasks1,
                          domain,
                          cpm,
                          R,
                          e,
                          2021,
                          aux_R);

    //parse_data p2;

    //p2 = team_sar_parser(infile2,state1, domain, -1);

    
    //p2.initial_state.action_tracker = p2.action_tracker;
    //p2.initial_state.loc_tracker = p2.loc_tracker;

    //p2.initial_state.plan_rec = true;

    //Tasks tasks2 = {
    //  {Task("SAR", Args({{"agent3", p2.initial_state.agents[2]},
    //                     {"agent2", p2.initial_state.agents[1]},
    //                     {"agent1", p2.initial_state.agents[0]}}),{"agent1","agent2","agent3"},{p2.initial_state.agents[0],p2.initial_state.agents[1],p2.initial_state.agents[2]})}};

    //auto cfm2 = cppMCTStrain(p2.team_plan,
    //                      p2.initial_state,
    //                      tasks2,
    //                      domain,
    //                      cpm,
    //                      R,
    //                      e,
    //                      2021,
    //                      aux_R);

    std::vector<CFM> cfms;
    cfms.push_back(cfm1);
    //cfms.push_back(cfm2);
    estimate_probs(cfms,cpm);
    json k = cpm;
    std::ofstream a("sar_cpm.json");
    a << std::setw(4) << k << std::endl;

    return EXIT_SUCCESS;
}
