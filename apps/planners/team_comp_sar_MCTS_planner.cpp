#include "domains/team_comp_sar.h"
#include <math.h>
#include <stdlib.h>
#include "plan_trace.h"
#include "plangrapher.h"
#include <istream>
#include <nlohmann/json.hpp>
#include <boost/program_options.hpp>
namespace po = boost::program_options;

using json = nlohmann::json;

using namespace std;

int main(int argc, char* argv[]) {
  int R = 30;
  double e = 0.4;
  double alpha = 0.5;
  int aux_R = 10;
  std::string map_json = "../apps/data_parsing/Saturn_map_info.json";
  std::string cfm_json;
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int)")
      ("exp_param,e",po::value<double>(),"The exploration parameter for the planner (double)")
      ("alpha,a", po::value<double>(), "default frequency measure for missing conditional probabilities in CFM (default)")
      ("map_json,m", po::value<std::string>(),"json file with map data (string)")
      ("cfm_json,j",po::value<std::string>(),"json file to parse CFM (string)")
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

    if (vm.count("alpha")) {
      alpha = vm["alpha"].as<double>();
    }

    if (vm.count("aux_r")) {
      aux_R = vm["aux_r"].as<int>();
    }

    if (vm.count("cfm_json")) {
      cfm_json = vm["cfm_json"].as<std::string>();
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
    std::string agent1 = "A1";
    std::string agent2 = "A2";
    std::string agent3 = "A3";
    state1.agents.push_back(agent1);
    state1.agents.push_back(agent2);
    state1.agents.push_back(agent3);
    
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


    for (auto a : state1.agents) {
      state1.role[a] = "NONE";

      state1.agent_loc[a] = state1.change_zone;

      state1.holding[a] = false;

      state1.time[a] = 0;

      state1.loc_tracker[a] = {};

      state1.action_tracker[a] = {};

      for (auto s : state1.zones) {
        if (s == state1.change_zone) {
          state1.visited[a][s] = 1;
        }
        else {
          state1.visited[a][s] = 0;
        }
      }
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
    
    CFM cfm = {};

    if (cfm_json != "") {
      std::ifstream i(cfm_json); 
      json j;
      i >> j;
      for (auto& [k1, v1] : j.items()) {
        for (auto& [k2,v2] : v1.items()) {
          cfm[k1][k2] = v2;
        }
      }
    }

    Tasks tasks = {
        {Task("SAR", Args({{"agent3", agent3},{"agent2", agent2},{"agent1",agent1}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
    auto pt = cppMCTShop(state1, tasks, domain, cfm,R,e,alpha,4021,aux_R);

    json j_tree = generate_plan_trace_tree(pt.first,pt.second,true,"team_comp_sar_trace_tree.json");
    generate_graph_from_json(j_tree, "team_comp_sar_tree_graph.png");
    generate_plan_trace(pt.first,pt.second,true,"team_comp_sar_trace.json");
    return EXIT_SUCCESS;
}
