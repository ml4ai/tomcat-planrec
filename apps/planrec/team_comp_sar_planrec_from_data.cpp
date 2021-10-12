#include <nlohmann/json.hpp>
#include "../data_parsing/parsers/team_comp_sar_parser.h"
#include <math.h>
#include <stdlib.h>
#include "plan_trace.h"
#include <istream>
#include "cppMCTSplanrec.h"
#include "plangrapher.h"
#include <boost/program_options.hpp>
namespace po = boost::program_options;

using json = nlohmann::json;

using namespace std;

int main(int argc, char* argv[]) {
  bool use_t = false; 
  int N = -1;
  int start = 0;
  int end = 0;
  int R = 30;
  double e = 0.4;
  double alpha = 0.5;
  int aux_R = 10;
  std::string infile = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-4.metadata";
  std::string map_json = "../apps/data_parsing/Saturn_map_info.json";
  std::string cfm_json;
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int)")
      ("exp_param,e",po::value<double>(),"The exploration parameter for the plan recognition algorithm (double)")
      ("alpha,a", po::value<double>(), "default frequency measure for missing conditional probabilities in CFM (default)")
      ("trace_size,N", po::value<int>(), "Sets trace size of N from beginning (int)")
      ("trace_segment,T", po::value<std::vector<int> >()->multitoken(), "Sets trace segments size by mission times (int int). Ignored if trace_size is set.")
      ("file,f",po::value<std::string>(),"file to parse (string)")
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
      e = vm["exp_para"].as<double>();
    }

    if (vm.count("alpha")) {
      alpha = vm["alpha"].as<double>();
    }

    if (vm.count("trace_size")) {
      N = vm["trace_size"].as<int>();
    } else {
      if (vm.count("trace_segment")) {
        const std::vector<int>& s = vm["trace_segment"].as<std::vector<int>>(); 
        use_t = true;
        start = s[0];
        end = s[1];
        if (start >= end) {
          std::cout << "Start time must be less than end time" << std::endl; 
          return 0;
        }
      }
    }

    if (vm.count("aux_r")) {
      aux_R = vm["aux_r"].as<int>();
    }

    if (vm.count("file")) {
      infile = vm["file"].as<std::string>();
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

    parse_data p;

    if (use_t) {
      std::pair<int,int> T = std::make_pair(start,end);
      p = team_sar_parser(infile,state1, domain, T);
    }
    else {
      p = team_sar_parser(infile,state1, domain, N);
    }

    
    p.initial_state.action_tracker = p.action_tracker;
    p.initial_state.loc_tracker = p.loc_tracker;

    Tasks tasks = {
      {Task("SAR", Args({{"agent3", p.initial_state.agents[2]},
                         {"agent2", p.initial_state.agents[1]},
                         {"agent1", p.initial_state.agents[0]}}),{"agent1","agent2","agent3"},{p.initial_state.agents[0],p.initial_state.agents[1],p.initial_state.agents[2]})}};

    auto pt = cppMCTSplanrec(p.team_plan,
                          p.initial_state,
                          tasks,
                          domain,
                          cfm,
                          R,
                          e,
                          alpha,
                          2021,
                          aux_R);
    json tree = generate_plan_trace_tree(pt.first,pt.second,true,"team_sar_pred_exp.json");
    generate_graph_from_json(tree, "team_sar_pred_exp_graph.png");
    return EXIT_SUCCESS;
}
