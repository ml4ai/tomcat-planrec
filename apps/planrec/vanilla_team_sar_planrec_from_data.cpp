#include <nlohmann/json.hpp>
#include "../data_parsing/parsers/vanilla_team_sar_parser.h"
#include <math.h>
#include <stdlib.h>
#include "plan_trace.h"
#include <istream>
#include "planrec.h"
#include "plangrapher.h"

using json = nlohmann::json;

using namespace std;

int main(int argc, char* argv[]) {
    int N;
    if (argc > 1) {
      N = strtol(argv[1], nullptr, 0);
    }
    else {
      N = 30;
    }
    
    int s;
    if (argc > 2) {
      s = strtol(argv[2],nullptr,0);
    }
    else {
      s = 5;
    }

    std::string infile;
    if (argc > 3) {
      infile = argv[3];
    }
    else {
      infile = "../apps/data_parsing/HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-2.metadata";
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
  
    auto domain = TeamSARDomain();
  
    auto p = team_sar_parser(infile,state1, domain, s);

    
    p.initial_state.action_tracker = p.action_tracker;
    p.initial_state.loc_tracker = p.loc_tracker;

    auto selector = TeamSARSelector();

    Tasks tasks = {
      {Task("SAR", Args({{"agent3", p.initial_state.agents[2]},
                         {"agent2", p.initial_state.agents[1]},
                         {"agent1", p.initial_state.agents[0]}}),{"agent1","agent2","agent3"},{p.initial_state.agents[0],p.initial_state.agents[1],p.initial_state.agents[2]})}};

    auto pt = cpphopPlanrecMCTS(p.trace,
                          p.initial_state,
                          tasks,
                          domain,
                          selector,
                          N,
                          0.4,
                          2021);
    json g = generate_plan_trace_tree(pt.first,pt.second,true,"team_sar_pred_exp.json");
    generate_graph_from_json(g, "team_sar_pred_exp_graph.png");
    return EXIT_SUCCESS;
}
