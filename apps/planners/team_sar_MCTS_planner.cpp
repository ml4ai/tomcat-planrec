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

    state1.change_zone = "CZ";
    state1.no_victim_zones.push_back(state1.change_zone);
    state1.no_victim_zones.push_back("NV");
    std::string area1 = "R1";
    std::string area2 = "R2";
    std::string area3 = "R3";
    std::string area4 = "Z4";
    std::string area5 = "Z5";
    std::string area6 = "Z6";
    std::string area7 = "Z7";
    std::string area8 = "Z8";
    std::string area9 = "Z9";
    std::string area10 = "Z10";
    std::string area11 = "Z11";
    std::string area12 = "MR12";

    state1.zones.push_back("CZ");
    state1.zones.push_back("NV");
    state1.zones.push_back(area1);
    state1.zones.push_back(area2);
    state1.zones.push_back(area3);
    state1.zones.push_back(area4);
    state1.zones.push_back(area5);
    state1.zones.push_back(area6);
    state1.zones.push_back(area7);
    state1.zones.push_back(area8);
    state1.zones.push_back(area9);
    state1.zones.push_back(area10);
    state1.zones.push_back(area11);
    state1.zones.push_back(area12);

    state1.rooms.push_back(area1);
    state1.rooms.push_back(area2);
    state1.rooms.push_back(area3);

    state1.multi_room_zones.push_back(area12);

    for (auto a : state1.agents) {
      state1.role[a] = "NONE";

      state1.agent_loc[a] = state1.change_zone;

      state1.holding[a] = false;

      state1.time[a] = 0;

      state1.loc_tracker[a] = {};

      for (auto s : state1.zones) {
        if (s == "CZ") {
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

    state1.c_max = 3;
    state1.r_max = 24;

    state1.action_tracker = {};

    auto domain = TeamSARDomain();

    auto selector = TeamSARSelector();

    Tasks tasks = {
        {Task("SAR", Args({{"agent3", agent3},{"agent2", agent2},{"agent1",agent1}}),{"agent1","agent2","agent3"})}};
    auto pt = cpphopMCTS(state1, tasks, domain, selector,N,e);

    json j = generate_plan_trace_tree(pt.first,pt.second,true,"team_sar_trace_tree.json");
    generate_graph_from_json(j, "team_sar_tree_graph.png");
    generate_plan_trace(pt.first,pt.second,true,"team_sar_trace.json");
    return EXIT_SUCCESS;
}
