#include "domains/team_sar.h"
#include <math.h>
#include <stdlib.h>
#include "plan_trace.h"
#include "plangrapher.h"
#include <nlohmann/json.hpp>

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
    double e;
    if (argc > 2) {
       e = strtod(argv[2],nullptr);
    }
    else {
      e = 0.4; 
    }

    auto state1 = SARState();
    state1.agents.push_back("A1");
    state1.agents.push_back("A2");
    state1.agents.push_back("A3");

    std::string area1 = "R1";
    std::string area2 = "R2";
    std::string area3 = "R3";
    std::string area4 = "R4";
    std::string area5 = "R5";
    std::string area6 = "R6";
    std::string area7 = "R7";
    std::string area8 = "R8";
    std::string area9 = "R9";
    std::string area10 = "R10";
    std::string area11 = "R11";
    std::string area12 = "R12";


    state1.rooms.push_back(area1);
    state1.rooms.push_back(area2);
    state1.rooms.push_back(area3);
    state1.rooms.push_back(area4);
    state1.rooms.push_back(area5);
    state1.rooms.push_back(area6);
    state1.rooms.push_back(area7);
    state1.rooms.push_back(area8);
    state1.rooms.push_back(area9);
    state1.rooms.push_back(area10);
    state1.rooms.push_back(area11);
    state1.rooms.push_back(area12);

    for (auto a : state1.agents) {
      state1.role[a] = "NONE";
      state1.read_role[a] = 0;
      state1.write_role[a] = 0;

      state1.agent_loc[a] = "entrance";
      state1.read_agent_loc[a] = 0;
      state1.write_agent_loc[a] = 0;

      state1.help_wake[a] = false;
      state1.read_help_wake[a] = 0;
      state1.write_help_wake[a] = 0;

      state1.holding[a] = "NONE";
      state1.read_holding[a] = 0;
      state1.write_holding[a] = 0;

      state1.c_seen[a] = {};
      state1.read_c_seen[a] = 0;
      state1.write_c_seen[a] = 0;

      state1.r_seen[a] = {};
      state1.read_r_seen[a] = 0;
      state1.write_r_seen[a] = 0;

      state1.time[a] = 0;
      state1.read_time[a] = 0;
      state1.write_time[a] = 0;

      state1.times_searched[a] = 0;
      state1.read_times_searched[a] = 0;
      state1.write_times_searched[a] = 0;
      
      state1.loc_tracker[a] = {};

      for (auto s : state1.rooms) {
        state1.visited[a][s] = 0;
        state1.read_visited[a][s] = 0;
        state1.write_visited[a][s] = 0;
      }
    }
    
    for (auto s : state1.rooms) {
      state1.c_vic_loc[s] = {}
      state1.read_c_vic_loc[s] = 0;
      state1.write_c_vic_loc[s] = 0;

      state1.r_vic_loc[s] = {}
      state1.read_r_vic_loc[s] = 0;
      state1.write_r_vic_loc[s] = 0;
    }

    std::string crit1 = "C1";
    std::string crit2 = "C2";
    std::string crit3 = "C3";

    std::string reg1 = "R1";
    std::string reg2 = "R2";
    std::string reg3 = "R3";
    std::string reg4 = "R4";
    std::string reg5 = "R5";
    std::string reg6 = "R6";
    std::string reg7 = "R7";
    std::string reg8 = "R8";
    std::string reg9 = "R9";
    std::string reg10 = "R10";
    std::string reg11 = "R11";
    std::string reg12 = "R12";
    std::string reg13 = "R13";
    std::string reg14 = "R14";
    std::string reg15 = "R15";
    std::string reg16 = "R16";
    std::string reg17 = "R17";
    std::string reg18 = "R18";
    std::string reg19 = "R19";
    std::string reg20 = "R20";
    std::string reg21 = "R21";
    std::string reg22 = "R22";
    std::string reg23 = "R23";
    std::string reg24 = "R24";

    state1.c_vic_loc[area4].push_back(crit1);
    state1.c_vic_loc[area5].push_back(crit2);
    state1.c_vic_loc[area2].push_back(crit3);

    state1.r_vic_loc[area11].push_back(reg1);
    state1.r_vic_loc[area1].push_back(reg2);
    state1.r_vic_loc[area3].push_back(reg3);
    state1.r_vic_loc[area8].push_back(reg4);
    state1.r_vic_loc[area6].push_back(reg5);
    state1.r_vic_loc[area12].push_back(reg6);
    state1.r_vic_loc[area10].push_back(reg7);
    state1.r_vic_loc[area12].push_back(reg8);
    state1.r_vic_loc[area3].push_back(reg9);
    state1.r_vic_loc[area9].push_back(reg10);
    state1.r_vic_loc[area10].push_back(reg11);
    state1.r_vic_loc[area10].push_back(reg12);
    state1.r_vic_loc[area12].push_back(reg13);
    state1.r_vic_loc[area1].push_back(reg14);
    state1.r_vic_loc[area7].push_back(reg15);
    state1.r_vic_loc[area9].push_back(reg16);
    state1.r_vic_loc[area7].push_back(reg17);
    state1.r_vic_loc[area6].push_back(reg18);
    state1.r_vic_loc[area10].push_back(reg19);
    state1.r_vic_loc[area7].push_back(reg20);
    state1.r_vic_loc[area6].push_back(reg21);
    state1.r_vic_loc[area12].push_back(reg22);
    state1.r_vic_loc[area9].push_back(reg23);
    state1.r_vic_loc[area3].push_back(reg24);

    auto domain = SARDomain();

    auto selector = SARSelector();

    Tasks tasks = {
        {Task("sweep_left_YF", Args({{"agent", "me"}}))}};
    auto pt = cpphopMCTS(state1, tasks, domain, selector,N,e);

    json j = generate_plan_trace_tree(pt.first,pt.second,true,"simple_sar_trace_tree.json");
    generate_graph_from_json(j, "simple_sar_tree_graph.png");
    generate_plan_trace(pt.first,pt.second,true,"simple_sar_trace.json");
    return EXIT_SUCCESS;
}
