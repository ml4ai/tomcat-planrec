#include "parsers/team_comp_sar_parser.h"
#include <istream>
#include <boost/program_options.hpp>
namespace po = boost::program_options;


int main(int argc, char* argv[]) {
  bool use_t = false; 
  int N = -1;
  int start = 0;
  int end = 0;
  std::string infile = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-4.metadata";
  std::string map_json = "../apps/data_parsing/Saturn_map_info.json";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("trace_size,N", po::value<int>(), "Sets trace size of N from beginning (int)")
      ("trace_segment,T", po::value<std::vector<int> >()->multitoken(), "Sets trace segments size by mission times (int int). Ignored if trace_size is set.")
      ("file,f",po::value<std::string>(),"file to parse (string)")
      ("map_json,m", po::value<std::string>(),"json file with map data (string)")
    ;

    po::variables_map vm;        
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
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
    if (vm.count("file")) {
      infile = vm["file"].as<std::string>();
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

  state1.c_triage_total = 0;

  state1.r_triage_total = 0;

  state1.c_max = 5;
  state1.r_max = 50;

  for (auto s : state1.zones) {
    state1.blocks_broken[s] = 0;

    state1.r_triaged_here[s] = false;

    state1.c_triaged_here[s] = false;

    state1.c_awake[s] = false;

  }

  auto domain = TeamSARDomain();
  if (use_t) {
    std::pair<int,int> T = std::make_pair(start,end);
    team_sar_parser(infile,state1, domain, T, true,"team_sar_ppt.json");
  }
  else {
    team_sar_parser(infile,state1, domain, N, true,"team_sar_ppt.json");
  }
  return EXIT_SUCCESS;
}
