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

    auto state1 = TeamSARState();
    std::string agent1 = "A1";
    std::string agent2 = "A2";
    std::string agent3 = "A3";
    state1.agents.push_back(agent1);
    state1.agents.push_back(agent2);
    state1.agents.push_back(agent3);

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

      state1.agent_loc[a] = "entrance";

      state1.holding[a] = "NONE";

      state1.c_seen[a] = {};

      state1.r_seen[a] = {};

      state1.time[a] = 0;

      state1.times_searched[a] = 0;
      
      state1.loc_tracker[a] = {};

      for (auto s : state1.rooms) {
        state1.visited[a][s] = 0;
      }
    }
    
    for (auto s : state1.rooms) {
      state1.c_vic_loc[s] = {};

      state1.r_vic_loc[s] = {};
      
      state1.room_blocks[s] = 0;

      state1.hall_blockage[s]["entrance"] = 0;
      state1.hall_blockage["entrance"][s] = 0;

      for (auto r : state1.rooms) {
        state1.hall_blockage[s][r] = 0;
        state1.hall_blockage[r][s] = 0;
      }
    }

    std::string crit1 = "C1";
    state1.obs[crit1] = false;

    std::string crit2 = "C2";
    state1.obs[crit2] = false;

    std::string crit3 = "C3";
    state1.obs[crit3] = true;

    std::string reg1 = "RV1";
    state1.obs[reg1] = false;
 
    std::string reg2 = "RV2";
    state1.obs[reg2] = false;
 
    std::string reg3 = "RV3";
    state1.obs[reg3] = false;
 
    std::string reg4 = "RV4";
    state1.obs[reg4] = false;
 
    std::string reg5 = "RV5";
    state1.obs[reg5] = true;
 
    std::string reg6 = "RV6";
    state1.obs[reg6] = true;
 
    std::string reg7 = "RV7";
    state1.obs[reg7] = true;
 
    std::string reg8 = "RV8";
    state1.obs[reg8] = true;
 
    std::string reg9 = "RV9";
    state1.obs[reg9] = false;
 
    std::string reg10 = "RV10";
    state1.obs[reg10] = false;
 
    std::string reg11 = "RV11";
    state1.obs[reg11] = false;
 
    std::string reg12 = "RV12";
    state1.obs[reg12] = false;
 
    std::string reg13 = "RV13";
    state1.obs[reg13] = false;
 
    std::string reg14 = "RV14";
    state1.obs[reg14] = true;
 
    std::string reg15 = "RV15";
    state1.obs[reg15] = true;
 
    std::string reg16 = "RV16";
    state1.obs[reg16] = false;
 
    std::string reg17 = "RV17";
    state1.obs[reg17] = false;
 
    std::string reg18 = "RV18";
    state1.obs[reg18] = false;
 
    std::string reg19 = "RV19";
    state1.obs[reg19] = true;
 
    std::string reg20 = "RV20";
    state1.obs[reg20] = true;
 
    std::string reg21 = "RV21";
    state1.obs[reg21] = false;
 
    std::string reg22 = "RV22";
    state1.obs[reg22] = true;
 
    std::string reg23 = "RV23";
    state1.obs[reg23] = false;
 
    std::string reg24 = "RV24";
    state1.obs[reg24] = true;

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

    state1.hall_blockage[area4][area12] = 15;
    state1.hall_blockage[area12][area4] = 15;

    state1.hall_blockage[area1][area4] = 2;
    state1.hall_blockage[area4][area1] = 2;

    state1.hall_blockage[area2][area8] = 12;
    state1.hall_blockage[area8][area2] = 12;

    state1.hall_blockage[area2][area11] = 8;
    state1.hall_blockage[area11][area2] = 8;

    state1.hall_blockage[area3][area11] = 8;
    state1.hall_blockage[area11][area3] = 8;

    state1.hall_blockage[area1][area9] = 8;
    state1.hall_blockage[area9][area1] = 8;

    state1.hall_blockage[area9][area10] = 3;
    state1.hall_blockage[area10][area9] = 3;

    state1.hall_blockage[area1][area8] = 16;
    state1.hall_blockage[area8][area1] = 16;

    state1.hall_blockage[area5][area6] = 6;
    state1.hall_blockage[area6][area5] = 6;

    state1.hall_blockage[area6][area8] = 7;
    state1.hall_blockage[area8][area6] = 7;

    state1.hall_blockage[area2][area12] = 2;
    state1.hall_blockage[area12][area2] = 2;

    state1.hall_blockage[area7][area9] = 4;
    state1.hall_blockage[area9][area7] = 4;

    state1.hall_blockage[area6][area11] = 6;
    state1.hall_blockage[area11][area6] = 6;

    state1.hall_blockage[area9][area12] = 3;
    state1.hall_blockage[area12][area9] = 3;

    state1.hall_blockage[area5][area10] = 4;
    state1.hall_blockage[area10][area5] = 4;

    state1.hall_blockage[area3][area9] = 4;
    state1.hall_blockage[area9][area3] = 4;

    state1.hall_blockage[area2][area3] = 6;
    state1.hall_blockage[area3][area2] = 6;

    state1.hall_blockage[area2][area9] = 8;
    state1.hall_blockage[area9][area2] = 8;

    state1.hall_blockage[area5][area12] = 7;
    state1.hall_blockage[area12][area5] = 7;

    state1.hall_blockage[area1][area11] = 2;
    state1.hall_blockage[area11][area1] = 2;

    state1.hall_blockage[area4][area11] = 4;
    state1.hall_blockage[area11][area4] = 4;

    state1.room_blocks[area1] = 9;
    state1.room_blocks[area2] = 5;
    state1.room_blocks[area3] = 6;
    state1.room_blocks[area5] = 2;
    state1.room_blocks[area6] = 4;
    state1.room_blocks[area7] = 7;
    state1.room_blocks[area10] = 4;
    state1.room_blocks[area11] = 2;
    state1.room_blocks[area12] = 5;

    state1.c_triage_total = 0;

    state1.r_triage_total = 0;

    state1.c_max = 3;
    state1.r_max = 24;

    auto domain = TeamSARDomain();

    auto selector = TeamSARSelector();

    Tasks tasks = {
        {Task("SAR", Args({{"agent3", agent3},{"agent2", agent2},{"agent1",agent1}}))}};
    auto pt = cpphopMCTS(state1, tasks, domain, selector,N,e);

    json j = generate_plan_trace_tree(pt.first,pt.second,true,"team_sar_trace_tree.json");
    generate_graph_from_json(j, "team_sar_tree_graph.png");
    generate_plan_trace(pt.first,pt.second,true,"team_sar_trace.json");
    return EXIT_SUCCESS;
}
