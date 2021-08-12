#include "parsers/vanilla_team_sar_parser.h"
#include <boost/program_options.hpp>
namespace po = boost::program_options;


int main(int argc, char* argv[]) {
  bool use_t = false; 
  int N = -1;
  int start = 0;
  int end = 0;
  std::string infile = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-4.metadata";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("trace_size,N", po::value<int>(), "Sets trace size of N from beginning")
      ("trace_segment,T", po::value<std::vector<int> >()->multitoken(), "Sets trace segments size by mission times. Ignored if trace_size is set.")
      ("file,f",po::value<std::string>(),"file to parse")
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
  }
  catch(std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  catch(...) {
    std::cerr << "Exception of unknown type!\n";
  }

  auto state1 = TeamSARState();

  state1.change_zone = "sga";
  state1.no_victim_zones.push_back(state1.change_zone);
  state1.no_victim_zones.push_back("ew");

  state1.rooms.push_back("acr");
  state1.rooms.push_back("br");
  state1.multi_room_zones.push_back("cf");
  state1.rooms.push_back("ds");
  state1.rooms.push_back("hcr");
  state1.rooms.push_back("jc");
  state1.rooms.push_back("kco");
  state1.multi_room_zones.push_back("kit");
  state1.multi_room_zones.push_back("lib");
  state1.multi_room_zones.push_back("llc");
  state1.rooms.push_back("mb");
  state1.rooms.push_back("mkcr");
  state1.rooms.push_back("o100");
  state1.rooms.push_back("o101");
  state1.rooms.push_back("oba");
  state1.rooms.push_back("r101");
  state1.rooms.push_back("r102");
  state1.rooms.push_back("r103");
  state1.rooms.push_back("r104");
  state1.rooms.push_back("r105");
  state1.rooms.push_back("r106");
  state1.rooms.push_back("r107");
  state1.rooms.push_back("r108");
  state1.rooms.push_back("r109");
  state1.rooms.push_back("r110");
  state1.multi_room_zones.push_back("sdc");
  state1.rooms.push_back("so");
  state1.rooms.push_back("srp");
  state1.rooms.push_back("sra");
  state1.rooms.push_back("srb");
  state1.rooms.push_back("src");
  state1.rooms.push_back("srd");
  state1.rooms.push_back("sre");
  state1.rooms.push_back("srf");
  state1.rooms.push_back("srg");
  state1.rooms.push_back("srh");
  state1.rooms.push_back("sri");
  state1.rooms.push_back("srj");
  state1.rooms.push_back("srk");
  state1.rooms.push_back("srl");
  state1.rooms.push_back("srm");
  state1.rooms.push_back("srn");
  state1.rooms.push_back("sro");
  state1.rooms.push_back("srq");
  state1.rooms.push_back("srr");
  state1.rooms.push_back("srs");
  state1.rooms.push_back("srt");
  state1.rooms.push_back("sru");
  state1.rooms.push_back("srv");
  state1.rooms.push_back("tkt");
  state1.rooms.push_back("wb");

  state1.c_triage_total = 0;

  state1.r_triage_total = 0;

  state1.c_max = 5;
  state1.r_max = 50;

  state1.action_tracker = {};

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
