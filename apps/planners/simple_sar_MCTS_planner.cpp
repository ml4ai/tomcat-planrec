#include "domains/simple_sar.h"
#include <math.h>
#include <stdlib.h>
#include "plan_trace.h"
#include "plangrapher.h"
#include <nlohmann/json.hpp>

using json = nlohmann::ordered_json;

using namespace std;

int main(int argc, char* argv[]) {
    int N;
    if (argc > 1) {
      N = strtol(argv[1], nullptr, 0);
    }
    else {
      N = 30;
    }
    int e;
    if (argc > 2) {
       e = strtol(argv[2],nullptr,0);
    }
    else {
      e = 0.4; 
    }

    auto state1 = SARState();
    state1.loc["me"] = "entrance";
    state1.visited["me"]["entrance"] = 1;
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

    state1.y_vic[area1] = 3;
    state1.y_vic[area2] = 1;
    state1.y_vic[area3] = 2;
    state1.y_vic[area4] = 0;
    state1.y_vic[area5] = 3;
    state1.y_vic[area6] = 2;
    state1.y_vic[area7] = 1;
    state1.y_vic[area8] = 2;
    state1.y_vic[area9] = 1;
    state1.y_vic[area10] = 1;
    state1.y_vic[area11] = 1;
    state1.y_vic[area12] = 3;

    state1.g_vic[area1] = 0;
    state1.g_vic[area2] = 5;
    state1.g_vic[area3] = 5;
    state1.g_vic[area4] = 2;
    state1.g_vic[area5] = 0;
    state1.g_vic[area6] = 5;
    state1.g_vic[area7] = 2;
    state1.g_vic[area8] = 3;
    state1.g_vic[area9] = 5;
    state1.g_vic[area10] = 3;
    state1.g_vic[area11] = 2;
    state1.g_vic[area12] = 0;

    state1.left_region.push_back(area1);
    state1.left_region.push_back(area2);
    state1.left_region.push_back(area3);
    state1.left_region.push_back(area4);

    state1.right_region.push_back(area5);
    state1.right_region.push_back(area6);
    state1.right_region.push_back(area7);
    state1.right_region.push_back(area8);

    state1.mid_region.push_back(area9);
    state1.mid_region.push_back(area10);
    state1.mid_region.push_back(area11);
    state1.mid_region.push_back(area12);

    state1.y_seen["me"] = 0;
    state1.g_seen["me"] = 0;
    state1.y_total = 0;
    state1.g_total = 0;
    state1.time = 0;
    state1.left_explored = false;
    state1.right_explored = false;
    state1.mid_explored = false;

    state1.times_searched = 0;

    state1.set_max_vic();

    state1.loc_tracker["left"] = {};
    state1.loc_tracker["right"] = {};
    state1.loc_tracker["mid"] = {};

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