#include "cppMCTShop.h"
#include "typedefs.h"
#include <math.h>
#include <nlohmann/json.hpp>
#include <string>
#include <algorithm>

// action struct
struct Action {
  std::string action;
  std::string agent;
  std::string area;
  std::string start;
  std::string duration;
};


// aux functions
std::string 
sample_loc(std::vector<std::string> allowable_zones,
           std::unordered_map<std::string, int> cost,
           int seed,
           double def = 1.0) {
  std::vector<double> w;
  for (auto a : allowable_zones) {
    if (cost.find(a) == cost.end()) {
      w.push_back(def);
    }
    else {
      w.push_back(1.0/(1.0 + cost[a]));
    }
  }
  std::mt19937 gen(seed);
  std::discrete_distribution<int> dist (w.begin(),w.end());
  int s = dist(gen);
  return allowable_zones[s];
}

std::string 
sample_loc(std::vector<std::string> allowable_zones,
           std::unordered_map<std::string, int> cost,
           double def = 1.0) {
  std::vector<double> w;
  for (auto a : allowable_zones) {
    if (cost.find(a) == cost.end()) {
      w.push_back(def);
    }
    else {
      w.push_back(1.0/(1.0 + cost[a]));
    }
  }
  std::random_device rd;
  std::mt19937 gen(rd());
  std::discrete_distribution<int> dist (w.begin(),w.end());
  int s = dist(gen);
  return allowable_zones[s];
}

bool sample_vic_seen(double p) {
  std::random_device rd;
  std::mt19937 gen(rd());
  std::bernoulli_distribution dist(p);
  return dist(gen);
}

bool sample_vic_seen(double p, int seed) {
  std::mt19937 gen(seed);
  std::bernoulli_distribution dist(p);
  return dist(gen);
}

template <class State> std::string get_team_comp(State state) {
  std::string team_comp = "";
  for (auto a : state.agents) {
    if(state.role[a] != "NONE") {
      if (state.role[a] == "Medical_Specialist") {
        team_comp += "m";
      }
      if (state.role[a] == "Hazardous_Material_Specialist") {
        team_comp += "h";
      }
      if (state.role[a] == "Search_Specialist") {
        team_comp += "s";
      }
    }
  } 
  sort(team_comp.begin(),team_comp.end());

  return team_comp;
}

// operators
template <class State> std::optional<State> triageReg(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  if (state.role[agent] == "Medical_Specialist" && state.agent_loc[agent] == area && 
      state.r_triage_total < state.r_max) {

    state.r_triage_total = state.r_triage_total + 1; 
    state.r_triaged_here[area] = true;
    state.time[agent] = end;
    if (state.dropped_off_here.find(area) != state.dropped_off_here.end()) {
      if (state.dropped_off_here[area] > 0) {
        state.dropped_off_here[area]--;
      }
    }
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }
    return state;

  }
  return std::nullopt;
}

template <class State> double triageReg(State pre_state,State post_state, Args args) {
  return 1;
}

template <class State> std::optional<State> wakeCrit(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  bool have_Medical_Specialist = false;
  bool all_here = true;
  for (auto a : state.agents) {
    if (state.role[a] == "Medical_Specialist") {
      have_Medical_Specialist = true;
    }
    
    if (state.agent_loc[a] != area) {
      all_here = false;
    }

    state.time[a] = end;
  }

  bool c_awake;
  if(state.c_awake.find(area) == state.c_awake.end()) {
    c_awake = false;
  }
  else {
    c_awake = state.c_awake[area];
  }
  if (all_here && have_Medical_Specialist && 
      state.c_triage_total < state.c_max && !c_awake) {
    state.c_awake[area] = true;
    for (auto a : state.agents) {
      if (!state.action_tracker[a].empty()) {
        state.action_tracker[a].pop_back();
      }
    }
    return state;
  }
  return std::nullopt;
}

template <class State> double wakeCrit(State pre_state,State post_state, Args args) {
  return 1;
}

template <class State> std::optional<State> triageCrit(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  bool c_awake;
  if(state.c_awake.find(area) == state.c_awake.end()) {
    c_awake = false;
  }
  else {
    c_awake = state.c_awake[area];
  }

  if (state.role[agent] == "Medical_Specialist" && state.agent_loc[agent] == area && 
      state.c_triage_total < state.c_max && c_awake) {

    state.c_triage_total = state.c_triage_total + 1; 
    state.c_triaged_here[area] = true;
    state.time[agent] = end;
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;

  }
  return std::nullopt;
}

template <class State> double triageCrit(State pre_state,State post_state, Args args) {
  return 1;
}

template <class State> std::optional<State> move(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.agent_loc[agent] == c_area) {

    state.agent_loc[agent] = n_area;

    if (state.visited[agent].find(n_area) == state.visited[agent].end()) {
      state.visited[agent][n_area] = 1;
      state.seed++;
    }
    else {
      state.visited[agent][n_area] = 1 + state.visited[agent][n_area];
      state.seed++;
    }
    state.time[agent] = end;

    if (!state.loc_tracker[agent].empty()) {
      state.loc_tracker[agent].pop_back();
    }
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double move(State pre_state, State post_state, Args args) {
  return 1;
}

template <class State> std::optional<State> break_block(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.agent_loc[agent] == area && state.role[agent] == "Hazardous_Material_Specialist") {

    if (state.blocks_broken.find(area) == state.blocks_broken.end()) {
      state.blocks_broken[area] = 1;
    }
    else {
      state.blocks_broken[area]++;
    }
    state.time[agent] = end;
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double break_block(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> pickup_vic(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.agent_loc[agent] == area && state.role[agent] == "Search_Specialist" &&
      state.r_triage_total < state.r_max && !state.holding[agent]) {
    
    state.holding[agent] = true;
    state.picked_up_from[agent] = area;
    if (state.picked_up_here.find(area) == state.picked_up_here.end()) {
      state.picked_up_here[area] = 1;
    }
    else {
      state.picked_up_here[area]++;
    }

    if (state.dropped_off_here.find(area) != state.dropped_off_here.end()) {
      if (state.dropped_off_here[area] > 0) {
        state.dropped_off_here[area]--;
      }
    }

    state.time[agent] = end;
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double pickup_vic(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> put_down_vic(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.agent_loc[agent] == area && state.role[agent] == "Search_Specialist" &&
      state.holding[agent]) {
    
    state.holding[agent] = false;
    if (state.vic_relocations[agent].find(state.picked_up_from[agent]) == state.vic_relocations[agent].end()) {
      state.vic_relocations[agent][state.picked_up_from[agent]][area] = 1;
    }
    else {
      if (state.vic_relocations[agent][state.picked_up_from[agent]].find(area) == state.vic_relocations[agent][state.picked_up_from[agent]].end()) {
        state.vic_relocations[agent][state.picked_up_from[agent]][area] = 1;
      }
      else {
        state.vic_relocations[agent][state.picked_up_from[agent]][area]++;
      }
    }

    if (state.dropped_off_here.find(area) == state.dropped_off_here.end()) {
      state.dropped_off_here[area] = 1;
    }
    else {
      state.dropped_off_here[area]++;
    }

    state.picked_up_from[agent] = "NONE";
    state.time[agent] = end;
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double put_down_vic(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> mark_opening_1(State state, Args args) {
  auto agent = args["agent"];
  auto area_placed = args ["area_placed"];
  auto area_marked = args["area_marked"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.agent_loc[agent] == area_placed && state.time[agent] < 900) {
    state.marked_opening_1[agent][area_placed][area_marked] = true;
    state.time[agent] = end;

    return state;
  } 
  return std::nullopt; 

}

template <class State> double mark_opening_1(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> mark_opening_2(State state, Args args) {
  auto agent = args["agent"];
  auto area_placed = args ["area_placed"];
  auto area_marked = args["area_marked"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.agent_loc[agent] == area_placed && state.time[agent] < 900) {
    state.marked_opening_2[agent][area_placed][area_marked] = true;
    state.time[agent] = end;

    return state;
  } 
  return std::nullopt; 

}

template <class State> double mark_opening_2(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> mark_opening_3(State state, Args args) {
  auto agent = args["agent"];
  auto area_placed = args ["area_placed"];
  auto area_marked = args["area_marked"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.agent_loc[agent] == area_placed && state.time[agent] < 900) {
    state.marked_opening_3[agent][area_placed][area_marked] = true;
    state.time[agent] = end;

    return state;
  } 
  return std::nullopt; 

}

template <class State> double mark_opening_3(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> mark_area_1(State state, Args args) {
  auto agent = args["agent"];
  auto area_marked = args["area_marked"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.agent_loc[agent] == area_marked && state.time[agent] < 900) {
    state.marked_area_1[agent][area_marked] = true;
    state.time[agent] = end;

    return state;
  } 
  return std::nullopt; 

}

template <class State> double mark_area_1(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> mark_area_2(State state, Args args) {
  auto agent = args["agent"];
  auto area_marked = args["area_marked"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.agent_loc[agent] == area_marked && state.time[agent] < 900) {
    state.marked_area_2[agent][area_marked] = true;
    state.time[agent] = end;

    return state;
  } 
  return std::nullopt; 

}

template <class State> double mark_area_2(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> mark_area_3(State state, Args args) {
  auto agent = args["agent"];
  auto area_marked = args["area_marked"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.agent_loc[agent] == area_marked && state.time[agent] < 900) {
    state.marked_area_3[agent][area_marked] = true;
    state.time[agent] = end;

    return state;
  } 
  return std::nullopt; 

}

template <class State> double mark_area_3(State pre_state, State post_state, Args args) {
    return 1;
}
template <class State> std::optional<State> change_to_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (!state.holding[agent]) {
  
    state.role[agent] = "Medical_Specialist";
    state.time[agent] = end;
    state.team_comp = get_team_comp(state);
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double change_to_Medical_Specialist(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> change_to_Hazardous_Material_Specialist(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (!state.holding[agent]) {
  
    state.role[agent] = "Hazardous_Material_Specialist";
    state.time[agent] = end;
    state.team_comp = get_team_comp(state);
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double change_to_Hazardous_Material_Specialist(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> change_to_Search_Specialist(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (!state.holding[agent]) {
  
    state.role[agent] = "Search_Specialist";
    state.time[agent] = end;
    state.team_comp = get_team_comp(state);
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double change_to_Search_Specialist(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> exit(State state, Args args) {
    auto agent = args["agent"];
    state.time[agent] = 900;
    if (!state.action_tracker[agent].empty()) {
      state.action_tracker[agent].pop_back();
    }

    return state;
}

template <class State> double exit(State pre_state, State post_state, Args args) {
    return 1;
}

// Methods
template <class State> cTasks SAR(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  return {"SAR_0",
    {Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
     Task("!exit", Args({{"agent",agent1},{"start","900"},{"duration","0"}}), {"agent","start","duration"},{agent1}),
     Task("!exit", Args({{"agent",agent2},{"start","900"},{"duration","0"}}), {"agent","start","duration"},{agent2}),
     Task("!exit", Args({{"agent",agent3},{"start","900"},{"duration","0"}}), {"agent","start","duration"},{agent3})}};
}

template <class State> cTasks no_class(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp.empty()) {
    return {"no_class_0",
      {Task("No_class", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_no_class(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_no_class_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("No_class", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_no_class(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_no_class_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("No_class", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks comp_change(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool role_change = false;
  bool act_available = false;
  int min_time = 900;
  std::vector<int> change_time = {};
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
      }
      if (act.action.substr(0,11) == "!change_to_") {
        role_change = true;
        change_time.push_back(stoi(act.start,nullptr));
      }
    }
  }
  
  if (act_available) {
    if (!role_change) {
      return {"NIL",{}};
    }
    else {
      if (!in(min_time,change_time)) {
        return {"NIL",{}};
      }
    }
  }

  if ((state.time[agent1] < 900 && !state.holding[agent1]) || (state.time[agent2] < 900 && !state.holding[agent2]) || (state.time[agent3] < 900 && !state.holding[agent3])) {
    std::string cond;
    if (state.team_comp.size() <= 2) {
      cond = "comp_change_0";
    }

    if (state.team_comp == "hhh") {
      cond = "comp_change_1";
    }
    if (state.team_comp == "hhm") {
      cond = "comp_change_2";
    }
    if (state.team_comp == "hhs") {
      cond = "comp_change_3";
    }
    if (state.team_comp == "hmm") {
      cond = "comp_change_4";
    }
    if (state.team_comp == "hms") {
      cond = "comp_change_5";
    }
    if (state.team_comp == "hss") {
      cond = "comp_change_6";
    }
    if (state.team_comp == "mmm") {
      cond = "comp_change_7";
    }
    if (state.team_comp == "mms") {
      cond = "comp_change_8";
    }
    if (state.team_comp == "mss") {
      cond = "comp_change_9";
    }
    if (state.team_comp == "sss") {
      cond = "comp_change_10";
    }

   return {cond,
          {Task("Team_composition_change", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks h(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "h") {
    return {"h_0",
      {Task("H", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_h(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_h_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("H", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_h(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_h_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("H", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks m(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "m") {
    return {"m_0",
      {Task("M", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_m(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_m_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("M", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_m(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_m_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("M", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks s(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "s") {
    return {"s_0",
      {Task("S", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_s(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_s_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("S", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_s(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_s_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("S", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hh(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hh") {
    return {"hh_0",
      {Task("HH", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hh(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hh_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HH", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hh(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_hh_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HH", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hm") {
    return {"hm_0",
      {Task("HM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hm_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_hm_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hs") {
    return {"hs_0",
      {Task("HS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hs",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_hs_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks mm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "mm") {
    return {"mm_0",
      {Task("MM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_mm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_mm_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_mm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_mm_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks ms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "ms") {
    return {"ms_0",
      {Task("MS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_ms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_ms_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_ms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_ms_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks ss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "ss") {
    return {"ss_0",
      {Task("SS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_ss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_ss_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("SS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_ss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_ss_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("SS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hhh(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hhh") {
    return {"hhh_0",
      {Task("HHH", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hhh(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hhh_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHH", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hhh(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_hhh_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHH", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hhm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hhm") {
    return {"hhm_0",
      {Task("HHM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hhm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hhm_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hhm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "group_hhm_0";
      }
      else {
        cond = "group_hhm_1";
      }
    }

    return {cond,
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hhs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hhs") {
    return {"hhs_0",
      {Task("HHS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hhs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hhs_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hhs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_hhs_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hmm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hmm") {
    return {"hmm_0",
      {Task("HMM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hmm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hmm_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HMM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hmm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "group_hmm_0";
      }
      else {
        cond = "group_hmm_1";
      }
    }

    return {cond,
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HMM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hms") {
    return {"hms_0",
      {Task("HMS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hms_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HMS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "group_hms_0";
      }
      else {
        cond = "group_hms_1";
      }
    }

    return {cond,
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HMS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "hss") {
    return {"hss_0",
      {Task("HSS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_hss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_hss_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_hss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_hss_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks mmm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "mmm") {
    return {"mmm_0",
      {Task("MMM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_mmm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_mmm_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MMM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_mmm(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "group_mmm_0";
      }
      else {
        cond = "group_mmm_1";
      }
    }

    return {cond,
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MMM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}


template <class State> cTasks mms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "mms") {
    return {"mms_0",
      {Task("MMS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_mms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_mms_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MMS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_mms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "group_mms_0";
      }
      else {
        cond = "group_mms_1";
      }
    }

    return {cond,
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MMS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks mss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "mss") {
    return {"mss_0",
      {Task("MSS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_mss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_mss_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_mss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "group_mss_0";
      }
      else {
        cond = "group_mss_1";
      }
    }

    return {cond,
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks sss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_comp == "sss") {
    return {"sss_0",
      {Task("SSS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3}),
      Task("Do_mission", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks single_agent_sss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool single_agent_tasks = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all" && act.action != "exit" &&
          act.action.substr(0,11) != "!change_to_") {
        single_agent_tasks = true;
      }
    }
  }
  
  if (act_available) {
    if (!single_agent_tasks) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"single_agent_sss_0",
          {Task("Assign_agent_for_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("SSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks group_sss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool group_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent == a) {
        group_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
  if (min_time < 900) {
    return {"group_sss_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("SSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks agent1_task(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool has_task = false;
  bool act_available = false;
  auto min_agent = agent1;
  int min_time = 900;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
        min_agent = a;
      }
      if (act.agent == agent1 && act.action != "exit" && 
          act.action.substr(0,11) != "!change_to_") {
        has_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!has_task) {
      return {"NIL",{}};
    }
  }
  else {
    min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
    if (min_time != state.time[agent1]) {
      min_agent = "NIL";
    }
  }

  if (state.time[agent1] < 900 && min_agent == agent1) {
    return {"U",
          {Task("Agent_1_task", Args({{"agent",agent1}}),{"agent"},{agent1})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks agent2_task(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool has_task = false;
  bool act_available = false;
  auto min_agent = agent2;
  int min_time = 900;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
        min_agent = a;
      }
      if (act.agent == agent2 && act.action != "exit" && 
          act.action.substr(0,11) != "!change_to_") {
        has_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!has_task) {
      return {"NIL",{}};
    }
  }
  else {
    min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
    if (min_time != state.time[agent2]) {
      min_agent = "NIL";
    }
  }

  if (state.time[agent2] < 900 && min_agent == agent2) {
    return {"U",
          {Task("Agent_2_task", Args({{"agent",agent2}}),{"agent"},{agent2})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks agent3_task(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool has_task = false;
  bool act_available = false;
  auto min_agent = agent3;
  int min_time = 900;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
        min_agent = a;
      }
      if (act.agent == agent3 && act.action != "exit" && 
          act.action.substr(0,11) != "!change_to_") {
        has_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!has_task) {
      return {"NIL",{}};
    }
  }
  else {
    min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
    if (min_time != state.time[agent3]) {
      min_agent = "NIL";
    }
  }

  if (state.time[agent3] < 900 && min_agent == agent3) {
    return {"U",
          {Task("Agent_3_task", Args({{"agent",agent3}}),{"agent"},{agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks no_class_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "NONE") {
    return {"no_class_task_0",
          {Task("No_class_task", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks h_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Hazardous_Material_Specialist") {
    return {"h_task_0",
          {Task("H_task", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks clear_area(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!break_block") {
      return {"NIL",{}};
    }
  }

  if (state.role[agent] == "Hazardous_Material_Specialist" && state.team_comp.size() >= 3 && 
      state.time[agent] < 900 && !in(state.agent_loc[agent],state.no_victim_zones)) {
      std::string cond;
      if (state.team_comp == "hhh") {
        cond = "clear_area_0";
      }
      if (state.team_comp == "hhm") {
        cond = "clear_area_1";
      }
      if (state.team_comp == "hhs") {
        cond = "clear_area_2";
      }
      if (state.team_comp == "hmm") {
        cond = "clear_area_3";
      }
      if (state.team_comp == "hms") {
        cond = "clear_area_4";
      }
      if (state.team_comp == "hss") {
        cond = "clear_area_5";
      }


      return {cond,
      {Task("Clear_area",Args({{"area",state.agent_loc[agent]},
                                      {"agent",agent}}),{"agent","area"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks break_blocks(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!break_block") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Hazardous_Material_Specialist" && state.time[agent] < 900) {
    std::string cond;

    int blocks_broken;
    if(state.blocks_broken.find(area) == state.blocks_broken.end()) {
      blocks_broken = 0;
    }
    else {
      blocks_broken = state.blocks_broken[area];
    }

    if (blocks_broken > 0) {
      if (state.team_comp == "hhh") {
        cond = "break_blocks_1";
      }
      if (state.team_comp == "hhm") {
        cond = "break_blocks_2";
      }
      if (state.team_comp == "hhs") {
        cond = "break_blocks_3";
      }
      if (state.team_comp == "hmm") {
        cond = "break_blocks_4";
      }
      if (state.team_comp == "hms") {
        cond = "break_blocks_5";
      }
      if (state.team_comp == "hss") {
        cond = "break_blocks_6";
      }
    }
    else {
      cond = "break_blocks_0";
    }

    return {cond,
      {Task("!break_block",Args({{"duration",duration},
                            {"start",start},
                            {"area",area},
                            {"agent",agent}}),{"agent","area","start","duration"},{agent}),
       Task("Clear_area",Args({{"area",area},
                               {"agent",agent}}),{"agent","area"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks done_breaking(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.role[agent] == "Hazardous_Material_Specialist") {
    std::string cond;

    int blocks_broken;
    if(state.blocks_broken.find(area) == state.blocks_broken.end()) {
      blocks_broken = 0;
    }
    else {
      blocks_broken = state.blocks_broken[area];
    }

    if (blocks_broken > 0) {
      if (state.team_comp == "hhh") {
        cond = "done_breaking_1";
      }
      if (state.team_comp == "hhm") {
        cond = "done_breaking_2";
      }
      if (state.team_comp == "hhs") {
        cond = "done_breaking_3";
      }
      if (state.team_comp == "hmm") {
        cond = "done_breaking_4";
      }
      if (state.team_comp == "hms") {
        cond = "done_breaking_5";
      }
      if (state.team_comp == "hss") {
        cond = "done_breaking_6";
      }
    }
    else {
      cond = "NIL";
    }
    if (state.time[agent] >= 900) {
      cond = "done_breaking_0";
    }

    return {cond,{}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks m_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Medical_Specialist") {
    return {"m_task_0",
          {Task("M_task", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks triage_critical(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!triageCrit") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "15";
    start = std::to_string(state.time[agent]);
  }

  bool c_awake;
  if(state.c_awake.find(state.agent_loc[agent]) == state.c_awake.end()) {
    c_awake = false;
  }
  else {
    c_awake = state.c_awake[state.agent_loc[agent]];
  }

  bool c_triaged_here;
  if(state.c_triaged_here.find(state.agent_loc[agent]) == state.c_triaged_here.end()) {
    c_triaged_here = false;
  }
  else {
    c_triaged_here = state.c_triaged_here[state.agent_loc[agent]];
  }

  if (state.role[agent] == "Medical_Specialist" && state.time[agent] < 900 &&
      c_awake && 
      !c_triaged_here &&
      state.c_triage_total < state.c_max) {
    std::string cond;
    if (in(state.agent_loc[agent],state.rooms)) {
      if (state.r_triage_total < state.r_max) {
        if (state.team_comp == "hhm") {
          cond = "triage_critical_0";
        }
        if (state.team_comp == "hmm") {
          cond = "triage_critical_1";
        }
        if (state.team_comp == "hms") {
          cond = "triage_critical_2";
        }
        if (state.team_comp == "mmm") {
          cond = "triage_critical_3";
        }
        if (state.team_comp == "mms") {
          cond = "triage_critical_4";
        }
        if (state.team_comp == "mss") {
          cond = "triage_critical_5";
        }
      }
      else {
        if (state.team_comp == "hhm") {
          cond = "triage_critical_6";
        }
        if (state.team_comp == "hmm") {
          cond = "triage_critical_7";
        }
        if (state.team_comp == "hms") {
          cond = "triage_critical_8";
        }
        if (state.team_comp == "mmm") {
          cond = "triage_critical_9";
        }
        if (state.team_comp == "mms") {
          cond = "triage_critical_10";
        }
        if (state.team_comp == "mss") {
          cond = "triage_critical_11";
        }
      }
    }
    else {
      if (state.team_comp == "hhm") {
        cond = "triage_critical_12";
      }
      if (state.team_comp == "hmm") {
        cond = "triage_critical_13";
      }
      if (state.team_comp == "hms") {
        cond = "triage_critical_14";
      }
      if (state.team_comp == "mmm") {
        cond = "triage_critical_15";
      }
      if (state.team_comp == "mms") {
        cond = "triage_critical_16";
      }
      if (state.team_comp == "mss") {
        cond = "triage_critical_17";
      }
    }
    return {cond,
      {Task("!triageCrit",Args({{"duration",duration},
                                {"start",start},
                                {"area",state.agent_loc[agent]},
                                {"agent",agent}}), {"agent","area","start","duration"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks triage_regs_in_area(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!triageReg") {
      return {"NIL",{}};
    }
  }
  if (state.role[agent] == "Medical_Specialist" && state.time[agent] < 900 &&
      !in(state.agent_loc[agent],state.no_victim_zones) &&
      state.r_triage_total < state.r_max) {
    std::string cond;

    bool c_awake;
    if(state.c_awake.find(state.agent_loc[agent]) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[state.agent_loc[agent]];
    }

    if (in(state.agent_loc[agent],state.rooms) && c_awake) {
      if (state.team_comp == "hhm") {
        cond = "triage_regs_in_area_6";
      }
      if (state.team_comp == "hmm") {
        cond = "triage_regs_in_area_7";
      }
      if (state.team_comp == "hms") {
        cond = "triage_regs_in_area_8";
      }
      if (state.team_comp == "mmm") {
        cond = "triage_regs_in_area_9";
      }
      if (state.team_comp == "mms") {
        cond = "triage_regs_in_area_10";
      }
      if (state.team_comp == "mss") {
        cond = "triage_regs_in_area_11";
      }
    }
    else {
      if (state.team_comp == "hhm") {
        cond = "triage_regs_in_area_0";
      }
      if (state.team_comp == "hmm") {
        cond = "triage_regs_in_area_1";
      }
      if (state.team_comp == "hms") {
        cond = "triage_regs_in_area_2";
      }
      if (state.team_comp == "mmm") {
        cond = "triage_regs_in_area_3";
      }
      if (state.team_comp == "mms") {
        cond = "triage_regs_in_area_4";
      }
      if (state.team_comp == "mss") {
        cond = "triage_regs_in_area_5";
      }
    }

    return {cond,
      {Task("Triage_regs_in_area",Args({{"area",state.agent_loc[agent]},
                            {"agent",agent}}), {"agent","area"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks triage_regs(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!triageReg") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "7";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Medical_Specialist" && state.time[agent] < 900 &&
      state.r_triage_total < state.r_max) {
    std::string cond;

    bool r_triaged_here;
    if(state.r_triaged_here.find(area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[area];
    }

    if (r_triaged_here) {
      if (state.team_comp == "hhm") {
        cond = "triage_regs_1";
      }
      if (state.team_comp == "hmm") {
        cond = "triage_regs_2";
      }
      if (state.team_comp == "hms") {
        cond = "triage_regs_3";
      }
      if (state.team_comp == "mmm") {
        cond = "triage_regs_4";
      }
      if (state.team_comp == "mms") {
        cond = "triage_regs_5";
      }
      if (state.team_comp == "mss") {
        cond = "triage_regs_6";
      }

    }
    else {
      cond = "triage_regs_0";
    }
    return {cond,
      {Task("!triageReg",Args({{"duration",duration},
                                {"start",start},
                                {"area",area},
                                {"agent",agent}}),{"agent","area","start","duration"},{agent}),
       Task("Triage_regs_in_area",Args({{"area",area},
                                {"agent",agent}}),{"agent","area"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks done_triaging(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];

  if (state.role[agent] == "Medical_Specialist") {
    std::string cond;;

    bool r_triaged_here;
    if(state.r_triaged_here.find(area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[area];
    }

    if (r_triaged_here) {
      if (state.team_comp == "hhm") {
        cond = "done_triaging_1";
      }
      if (state.team_comp == "hmm") {
        cond = "done_triaging_2";
      }
      if (state.team_comp == "hms") {
        cond = "done_triaging_3";
      }
      if (state.team_comp == "mmm") {
        cond = "done_triaging_4";
      }
      if (state.team_comp == "mms") {
        cond = "done_triaging_5";
      }
      if (state.team_comp == "mss") {
        cond = "done_triaging_6";
      }
    }
    else {
      cond = "NIL";
    }
    if (state.time[agent] >= 900) {
      cond = "done_triaging_0";
    }

    return {cond,{}};
  }
  return {"NIL",{}};
}

template <class State> cTasks s_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Search_Specialist") {
    return {"s_task_0",
          {Task("S_task", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks relocate_victim(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!pickup_vic") {
      return {"NIL",{}};
    }
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900 &&
      !in(state.agent_loc[agent],state.no_victim_zones) &&
      state.r_triage_total < state.r_max && !state.holding[agent]) {
    std::string cond;
    if (state.team_comp == "hhs") {
      cond = "relocate_victim_0";
    }
    if (state.team_comp == "hms") {
      cond = "relocate_victim_1";
    }
    if (state.team_comp == "hss") {
      cond = "relocate_victim_2";
    }
    if (state.team_comp == "mms") {
      cond = "relocate_victim_3";
    }
    if (state.team_comp == "mss") {
      cond = "relocate_victim_4";
    }
    if (state.team_comp == "sss") {
      cond = "relocate_victim_5";
    }

    return {cond,
      {Task("Relocate_vic",Args({{"agent",agent}}),{"agent"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks resume_relocate_victim(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!move" && act.action != "!put_down_vic") {
      return {"NIL",{}};
    }
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900 &&
      !in(state.agent_loc[agent],state.no_victim_zones) &&
      state.holding[agent]) {

    return {"resume_relocate_victim_0",
      {Task("Relocate_vic",Args({{"agent",agent}}),{"agent"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks pickup_victim(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!pickup_vic") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900 &&
      !state.holding[agent]) {

    return {"pickup_victim_0",
      {Task("!pickup_vic",Args({{"duration",duration},
                                {"start",start},
                                {"area",state.agent_loc[agent]},
                                {"agent",agent}}),{"agent","area","start","duration"},{agent}),
       Task("Relocate_vic",Args({{"agent",agent}}), {"agent"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks move_victim(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!move") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "4";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900 &&
      state.holding[agent]) {

    std::string n_area;
    if (state.loc_tracker[agent].empty()) {
      do {
        n_area = sample_loc(state.graph[state.agent_loc[agent]],state.visited[agent],state.seed);
        state.seed++;
      }
      while(state.agent_loc[agent] == state.class_only_boundary && in(n_area,state.no_victim_zones));
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    std::string cond;
    if (state.team_comp == "hhs") {
      cond = "move_victim_0";
    }
    if (state.team_comp == "hms") {
      cond = "move_victim_1";
    }
    if (state.team_comp == "hss") {
      cond = "move_victim_2";
    }
    if (state.team_comp == "mms") {
      cond = "move_victim_3";
    }
    if (state.team_comp == "mss") {
      cond = "move_victim_4";
    }
    if (state.team_comp == "sss") {
      cond = "move_victim_5";
    }

    return {cond,
      {Task("!move",Args({{"duration",duration},
                          {"start",start},
                          {"n_area",n_area},
                          {"c_area",state.agent_loc[agent]},
                          {"agent",agent}}),{"agent","c_area","n_area","start","duration"},{agent}),
       Task("Relocate_vic",Args({{"agent",agent}}),{"agent"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks putdown_victim(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!put_down_vic") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900 &&
      state.holding[agent]) {

    std::string cond;
    if (state.team_comp == "hhs") {
      cond = "putdown_victim_0";
    }
    if (state.team_comp == "hms") {
      cond = "putdown_victim_1";
    }
    if (state.team_comp == "hss") {
      cond = "putdown_victim_2";
    }
    if (state.team_comp == "mms") {
      cond = "putdown_victim_3";
    }
    if (state.team_comp == "mss") {
      cond = "putdown_victim_4";
    }
    if (state.team_comp == "sss") {
      cond = "putdown_victim_5";
    }

    return {cond,
      {Task("!put_down_vic",Args({{"duration",duration},
                                {"start",start},
                                {"area",state.agent_loc[agent]},
                                {"agent",agent}}),{"agent","area","start","duration"},{agent})}};
  }  
  return {"NIL",{}};
}

template<class State> cTasks need_to_do_something_else(State state,Args args) {
  auto agent = args["agent"];
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action == "!put_down_vic" || act.action == "!move") {
      return {"NIL",{}};
    }
  }
  return {"need_to_do_something_else_0", {}};

}

template <class State> cTasks no_time_to_putdown(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Search_Specialist" && state.time[agent] >= 900 &&
      state.holding[agent]) {

    return {"no_time_to_putdown_0",{}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks move_agent(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!move") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  std::string n_area;
  if (state.loc_tracker[agent].empty()) {
      do {
        n_area = sample_loc(state.graph[state.agent_loc[agent]],state.visited[agent],state.seed);
        state.seed++;
      }
      while(state.team_comp.size() < 3 && n_area == state.class_only_boundary);
  }
  else {
    n_area = state.loc_tracker[agent].back();
  }

  if (state.time[agent] < 900) {
    std::string cond = "move_agent_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "move_agent_1";
        }
        if (state.team_comp == "hhm") {
          cond = "move_agent_2";
        }
        if (state.team_comp == "hhs") {
          cond = "move_agent_3";
        }
        if (state.team_comp == "hmm") {
          cond = "move_agent_4";
        }
        if (state.team_comp == "hms") {
          cond = "move_agent_5";
        }
        if (state.team_comp == "hss") {
          cond = "move_agent_6";
        }
      }

      if (state.role[agent] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "move_agent_7";
        }
        if (state.team_comp == "hmm") {
          cond = "move_agent_8";
        }
        if (state.team_comp == "hms") {
          cond = "move_agent_9";
        }
        if (state.team_comp == "mmm") {
          cond = "move_agent_10";
        }
        if (state.team_comp == "mms") {
          cond = "move_agent_11";
        }
        if (state.team_comp == "mss") {
          cond = "move_agent_12";
        }
      }

      if (state.role[agent] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "move_agent_13";
        }
        if (state.team_comp == "hms") {
          cond = "move_agent_14";
        }
        if (state.team_comp == "hss") {
          cond = "move_agent_15";
        }
        if (state.team_comp == "mms") {
          cond = "move_agent_16";
        }
        if (state.team_comp == "mss") {
          cond = "move_agent_17";
        }
        if (state.team_comp == "sss") {
          cond = "move_agent_18";
        }
      }

    }

    return {cond,
      {Task("!move",Args({{"duration",duration},
                            {"start",start},
                            {"n_area",n_area},
                            {"c_area",state.agent_loc[agent]},
                            {"agent",agent}}), {"agent","c_area","n_area","start","duration"},{agent})}};
  }  
  return {"NIL",{}};
}

template <class State> cTasks agent1_change_role(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool change_role = false;
  bool act_available = false;
  auto min_agent = agent1;
  int min_time = 900;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
        min_agent = a;
      }
      if (act.action.substr(0,11) == "!change_to_" && act.agent == agent1) {
        change_role = true;
      }
    }
  }
  
  if (act_available) {
    if (!change_role) {
      return {"NIL",{}};
    }
  }
  else {
    min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
    if (min_time != state.time[agent1]) {
      min_agent = "NIL";
    }
  }

  if (state.time[agent1] < 900 && !state.holding[agent1] && min_agent == agent1) {
    std::string cond = "agent1_change_role_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent1] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "agent1_change_role_1";
        }
        if (state.team_comp == "hhm") {
          cond = "agent1_change_role_2";
        }
        if (state.team_comp == "hhs") {
          cond = "agent1_change_role_3";
        }
        if (state.team_comp == "hmm") {
          cond = "agent1_change_role_4";
        }
        if (state.team_comp == "hms") {
          cond = "agent1_change_role_5";
        }
        if (state.team_comp == "hss") {
          cond = "agent1_change_role_6";
        }
      }

      if (state.role[agent1] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "agent1_change_role_7";
        }
        if (state.team_comp == "hmm") {
          cond = "agent1_change_role_8";
        }
        if (state.team_comp == "hms") {
          cond = "agent1_change_role_9";
        }
        if (state.team_comp == "mmm") {
          cond = "agent1_change_role_10";
        }
        if (state.team_comp == "mms") {
          cond = "agent1_change_role_11";
        }
        if (state.team_comp == "mss") {
          cond = "agent1_change_role_12";
        }
      }

      if (state.role[agent1] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "agent1_change_role_13";
        }
        if (state.team_comp == "hms") {
          cond = "agent1_change_role_14";
        }
        if (state.team_comp == "hss") {
          cond = "agent1_change_role_15";
        }
        if (state.team_comp == "mms") {
          cond = "agent1_change_role_16";
        }
        if (state.team_comp == "mss") {
          cond = "agent1_change_role_17";
        }
        if (state.team_comp == "sss") {
          cond = "agent1_change_role_18";
        }
      }
    }

    return {cond,
          {Task("Agent_1_change_role", Args({{"agent",agent1}}),{"agent"},{agent1})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks agent2_change_role(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool change_role = false;
  bool act_available = false;
  auto min_agent = agent2;
  int min_time = 900;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
        min_agent = a;
      }
      if (act.action.substr(0,11) == "!change_to_" && act.agent == agent2) {
        change_role = true;
      }
    }
  }
  
  if (act_available) {
    if (!change_role) {
      return {"NIL",{}};
    }
  }
  else {
    min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
    if (min_time != state.time[agent2]) {
      min_agent = "NIL";
    }
  }

  if (state.time[agent2] < 900 && !state.holding[agent2] && min_agent == agent2) {
    std::string cond = "agent2_change_role_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent2] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "agent2_change_role_1";
        }
        if (state.team_comp == "hhm") {
          cond = "agent2_change_role_2";
        }
        if (state.team_comp == "hhs") {
          cond = "agent2_change_role_3";
        }
        if (state.team_comp == "hmm") {
          cond = "agent2_change_role_4";
        }
        if (state.team_comp == "hms") {
          cond = "agent2_change_role_5";
        }
        if (state.team_comp == "hss") {
          cond = "agent2_change_role_6";
        }
      }

      if (state.role[agent2] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "agent2_change_role_7";
        }
        if (state.team_comp == "hmm") {
          cond = "agent2_change_role_8";
        }
        if (state.team_comp == "hms") {
          cond = "agent2_change_role_9";
        }
        if (state.team_comp == "mmm") {
          cond = "agent2_change_role_10";
        }
        if (state.team_comp == "mms") {
          cond = "agent2_change_role_11";
        }
        if (state.team_comp == "mss") {
          cond = "agent2_change_role_12";
        }
      }

      if (state.role[agent2] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "agent2_change_role_13";
        }
        if (state.team_comp == "hms") {
          cond = "agent2_change_role_14";
        }
        if (state.team_comp == "hss") {
          cond = "agent2_change_role_15";
        }
        if (state.team_comp == "mms") {
          cond = "agent2_change_role_16";
        }
        if (state.team_comp == "mss") {
          cond = "agent2_change_role_17";
        }
        if (state.team_comp == "sss") {
          cond = "agent2_change_role_18";
        }
      }
    }

    return {cond,
          {Task("Agent_2_change_role", Args({{"agent",agent2}}),{"agent"},{agent2})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks agent3_change_role(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool change_role = false;
  bool act_available = false;
  auto min_agent = agent3;
  int min_time = 900;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (stoi(act.start,nullptr) < min_time) {
        min_time = stoi(act.start,nullptr);
        min_agent = a;
      }
      if (act.action.substr(0,11) == "!change_to_" && act.agent == agent3) {
        change_role = true;
      }
    }
  }
  
  if (act_available) {
    if (!change_role) {
      return {"NIL",{}};
    }
  }
  else {
    min_time = std::min({state.time[agent1], state.time[agent2], state.time[agent3]});
    if (min_time != state.time[agent3]) {
      min_agent = "NIL";
    }
  }

  if (state.time[agent3] < 900 && !state.holding[agent3] && min_agent == agent3) {
    std::string cond = "agent3_change_role_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent3] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "agent3_change_role_1";
        }
        if (state.team_comp == "hhm") {
          cond = "agent3_change_role_2";
        }
        if (state.team_comp == "hhs") {
          cond = "agent3_change_role_3";
        }
        if (state.team_comp == "hmm") {
          cond = "agent3_change_role_4";
        }
        if (state.team_comp == "hms") {
          cond = "agent3_change_role_5";
        }
        if (state.team_comp == "hss") {
          cond = "agent3_change_role_6";
        }
      }

      if (state.role[agent3] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "agent3_change_role_7";
        }
        if (state.team_comp == "hmm") {
          cond = "agent3_change_role_8";
        }
        if (state.team_comp == "hms") {
          cond = "agent3_change_role_9";
        }
        if (state.team_comp == "mmm") {
          cond = "agent3_change_role_10";
        }
        if (state.team_comp == "mms") {
          cond = "agent3_change_role_11";
        }
        if (state.team_comp == "mss") {
          cond = "agent3_change_role_12";
        }
      }

      if (state.role[agent3] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "agent3_change_role_13";
        }
        if (state.team_comp == "hms") {
          cond = "agent3_change_role_14";
        }
        if (state.team_comp == "hss") {
          cond = "agent3_change_role_15";
        }
        if (state.team_comp == "mms") {
          cond = "agent3_change_role_16";
        }
        if (state.team_comp == "mss") {
          cond = "agent3_change_role_17";
        }
        if (state.team_comp == "sss") {
          cond = "agent3_change_role_18";
        }
      }
    }

    return {cond,
          {Task("Agent_3_change_role", Args({{"agent",agent3}}),{"agent"},{agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks changing_role(State state, Args args) {
  auto agent = args["agent"];

  if (state.time[agent] < 900) {
    return {"changing_role_0",
          {Task("Changing_role", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks moving_to_change_zone(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    auto act = state.action_tracker[agent].back();
    if (act.action != "!move") {
      return {"NIL",{}};
    } 
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  std::string n_area;
  if (state.loc_tracker[agent].empty()) {
      n_area = sample_loc(state.graph[state.agent_loc[agent]],state.dist_from_change_zone,state.seed);
      state.seed++;
  }
  else {
    n_area = state.loc_tracker[agent].back();
  }
  if (state.time[agent] < 900 && state.agent_loc[agent] != state.change_zone) {
    return {"moving_to_change_zone_0",
          {Task("!move", Args({{"agent",agent},
                               {"c_area",state.agent_loc[agent]},
                               {"n_area",n_area},
                               {"start",start},
                               {"duration",duration}}),{"agent",
                                                        "c_area",
                                                        "n_area",
                                                        "start",
                                                        "duration"},{agent}),
           Task("Changing_role", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks picking_role(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    auto act = state.action_tracker[agent].back();
    if (act.action.substr(0,11) != "!change_to_") {
      return {"NIL",{}};
    } 
  }

  if (state.time[agent] < 900 && state.agent_loc[agent] == state.change_zone) {
    return {"picking_role_0",
          {Task("Pick_new_role", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks no_time_to_change(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    auto act = state.action_tracker[agent].back();
    if (act.action != "!exit") {
      return {"NIL",{}};
    } 
  }

  if (state.time[agent] >= 900) {
    return {"no_time_to_change_0",{}};
  }
  return {"NIL",{}};
}

template <class State> cTasks all_task(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool has_task = true;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != "all") {
        has_task = false;
      }
    }
  }
  
  if (act_available) {
    if (!has_task) {
      return {"NIL",{}};
    }
  }


  if (state.time[agent1] < 900 && !in(state.agent_loc[agent1],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[agent1];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "all_task_0";
      }
      else {
        cond = "all_task_1";
      }
    }

    return {cond,
           {Task("All_task", Args({{"agent1",agent1},
                                   {"agent2",agent2},
                                   {"agent3",agent3}}),{"agent1",
                                                        "agent2",
                                                        "agent3"}, {agent1,
                                                                    agent2,
                                                                    agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks wake_crit_vic(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.action != "!wakeCrit") {
        return {"NIL",{}}; 
      }
    }
  }

  auto min_agent = agent1;
  std::string duration = "1";
  int start_num = std::max({state.time[agent1],state.time[agent2],state.time[agent3]});
  std::string start = std::to_string(start_num);
  if (!act_available) {
    auto min_time = state.time[agent1];
    for (auto a : state.agents) {
      if (state.time[a] < min_time) {
        min_agent = a;
        min_time = state.time[a];
      }
    }
  }
  else { 
    auto act = state.action_tracker[min_agent].back();
    duration = act.duration;
    start = act.start;
  }

  if (state.time[min_agent] < 900 && !in(state.agent_loc[min_agent],state.no_victim_zones) &&
      state.team_comp.size() >= 3 && state.team_comp.find("m") != std::string::npos) {
    std::string c_vic_area = state.agent_loc[min_agent];

    bool c_awake;
    if(state.c_awake.find(c_vic_area) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[c_vic_area];
    }

    bool in_room = in(c_vic_area,state.rooms);
    if ((!in_room && 
        !in(c_vic_area,state.multi_room_zones)) ||
        c_awake ||
        state.c_triage_total >= state.c_max) {
      c_vic_area = "NONE";
    }
    bool all_gathered = true;
    for (auto a : state.agents) {
      if (state.agent_loc[a] != c_vic_area) {
        all_gathered = false;
      } 
    }
    std::string cond = "NIL";

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        cond = "wake_crit_vic_0";
      }
      else {
        cond = "wake_crit_vic_1";
      }
    }
 
    return {cond,
          {Task("!wakeCrit", Args({{"duration",duration},
                                     {"start",start},
                                     {"area",state.agent_loc[min_agent]},
                                     {"agent3",agent3},
                                     {"agent2",agent2},
                                     {"agent1",agent1}}), {"agent1","agent2","agent3","area","start","duration"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks out_of_time(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
    }
  }

  auto min_agent = agent1;
  if (!act_available) {
    auto min_time = state.time[agent1];
    for (auto a : state.agents) {
      if (state.time[a] < min_time) {
        min_agent = a;
        min_time = state.time[a];
      }
    }
  }
  else { 
    if (state.action_tracker[min_agent].empty()) {
      return {"NIL",{}};
    }
    Action act = state.action_tracker[min_agent].back();
    if (act.action == "!exit") {
      return {"out_of_time_0",{}};
    }
    return {"NIL",{}};
  }

  if (state.time[min_agent] >= 900) {
    return {"out_of_time_0",{}};
  }
  return {"NIL",{}};
}

template <class State> cTasks choose_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!change_to_Medical_Specialist") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (!state.holding[agent] && state.agent_loc[agent] == state.change_zone) {
    std::string cond = "choose_Medical_Specialist_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "choose_Medical_Specialist_1";
        }
        if (state.team_comp == "hhm") {
          cond = "choose_Medical_Specialist_2";
        }
        if (state.team_comp == "hhs") {
          cond = "choose_Medical_Specialist_3";
        }
        if (state.team_comp == "hmm") {
          cond = "choose_Medical_Specialist_4";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Medical_Specialist_5";
        }
        if (state.team_comp == "hss") {
          cond = "choose_Medical_Specialist_6";
        }
      }

      if (state.role[agent] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "choose_Medical_Specialist_7";
        }
        if (state.team_comp == "hmm") {
          cond = "choose_Medical_Specialist_8";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Medical_Specialist_9";
        }
        if (state.team_comp == "mmm") {
          cond = "choose_Medical_Specialist_10";
        }
        if (state.team_comp == "mms") {
          cond = "choose_Medical_Specialist_11";
        }
        if (state.team_comp == "mss") {
          cond = "choose_Medical_Specialist_12";
        }
      }

      if (state.role[agent] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "choose_Medical_Specialist_13";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Medical_Specialist_14";
        }
        if (state.team_comp == "hss") {
          cond = "choose_Medical_Specialist_15";
        }
        if (state.team_comp == "mms") {
          cond = "choose_Medical_Specialist_16";
        }
        if (state.team_comp == "mss") {
          cond = "choose_Medical_Specialist_17";
        }
        if (state.team_comp == "sss") {
          cond = "choose_Medical_Specialist_18";
        }
      }
    }

    return {cond,
      {Task("!change_to_Medical_Specialist", Args({{"duration", duration},
                                     {"start",start},
                                     {"agent",agent}}), {"agent","start","duration"},{agent})}};
  }
  return {"NIL",{}};

}

template <class State> cTasks choose_Hazardous_Material_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!change_to_Hazardous_Material_Specialist") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (!state.holding[agent] && state.agent_loc[agent] == state.change_zone) {
    std::string cond = "choose_Hazardous_Material_Specialist_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "choose_Hazardous_Material_Specialist_1";
        }
        if (state.team_comp == "hhm") {
          cond = "choose_Hazardous_Material_Specialist_2";
        }
        if (state.team_comp == "hhs") {
          cond = "choose_Hazardous_Material_Specialist_3";
        }
        if (state.team_comp == "hmm") {
          cond = "choose_Hazardous_Material_Specialist_4";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Hazardous_Material_Specialist_5";
        }
        if (state.team_comp == "hss") {
          cond = "choose_Hazardous_Material_Specialist_6";
        }
      }

      if (state.role[agent] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "choose_Hazardous_Material_Specialist_7";
        }
        if (state.team_comp == "hmm") {
          cond = "choose_Hazardous_Material_Specialist_8";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Hazardous_Material_Specialist_9";
        }
        if (state.team_comp == "mmm") {
          cond = "choose_Hazardous_Material_Specialist_10";
        }
        if (state.team_comp == "mms") {
          cond = "choose_Hazardous_Material_Specialist_11";
        }
        if (state.team_comp == "mss") {
          cond = "choose_Hazardous_Material_Specialist_12";
        }
      }

      if (state.role[agent] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "choose_Hazardous_Material_Specialist_13";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Hazardous_Material_Specialist_14";
        }
        if (state.team_comp == "hss") {
          cond = "choose_Hazardous_Material_Specialist_15";
        }
        if (state.team_comp == "mms") {
          cond = "choose_Hazardous_Material_Specialist_16";
        }
        if (state.team_comp == "mss") {
          cond = "choose_Hazardous_Material_Specialist_17";
        }
        if (state.team_comp == "sss") {
          cond = "choose_Hazardous_Material_Specialist_18";
        }
      }
    }

    return {cond,
      {Task("!change_to_Hazardous_Material_Specialist", Args({{"duration", duration},
                                     {"start",start},
                                     {"agent",agent}}), {"agent","start","duration"},{agent})}};
  }
  return {"NIL",{}};

}

template <class State> cTasks choose_Search_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    Action act = state.action_tracker[agent].back();
    if (act.action != "!change_to_Search_Specialist") {
      return {"NIL",{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (!state.holding[agent] && state.agent_loc[agent] == state.change_zone) {
    std::string cond = "choose_Search_Specialist_0";
    if (state.team_comp.size() >= 3) {
      if (state.role[agent] == "Hazardous_Material_Specialist") {
        if (state.team_comp == "hhh") {
          cond = "choose_Search_Specialist_1";
        }
        if (state.team_comp == "hhm") {
          cond = "choose_Search_Specialist_2";
        }
        if (state.team_comp == "hhs") {
          cond = "choose_Search_Specialist_3";
        }
        if (state.team_comp == "hmm") {
          cond = "choose_Search_Specialist_4";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Search_Specialist_5";
        }
        if (state.team_comp == "hss") {
          cond = "choose_Search_Specialist_6";
        }
      }

      if (state.role[agent] == "Medical_Specialist") {
        if (state.team_comp == "hhm") {
          cond = "choose_Search_Specialist_7";
        }
        if (state.team_comp == "hmm") {
          cond = "choose_Search_Specialist_8";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Search_Specialist_9";
        }
        if (state.team_comp == "mmm") {
          cond = "choose_Search_Specialist_10";
        }
        if (state.team_comp == "mms") {
          cond = "choose_Search_Specialist_11";
        }
        if (state.team_comp == "mss") {
          cond = "choose_Search_Specialist_12";
        }
      }

      if (state.role[agent] == "Search_Specialist") {
        if (state.team_comp == "hhs") {
          cond = "choose_Search_Specialist_13";
        }
        if (state.team_comp == "hms") {
          cond = "choose_Search_Specialist_14";
        }
        if (state.team_comp == "hss") {
          cond = "choose_Search_Specialist_15";
        }
        if (state.team_comp == "mms") {
          cond = "choose_Search_Specialist_16";
        }
        if (state.team_comp == "mss") {
          cond = "choose_Search_Specialist_17";
        }
        if (state.team_comp == "sss") {
          cond = "choose_Search_Specialist_18";
        }
      }
    }

    return {cond,
      {Task("!change_to_Search_Specialist", Args({{"duration", duration},
                                     {"start",start},
                                     {"agent",agent}}),{"agent","start","duration"},{agent})}};
  }
  return {"NIL",{}};

}

class TeamSARState {
  public:

    // *** Static ***
    std::vector<std::string> agents;

    std::vector<std::string> zones;

    std::vector<std::string> rooms;

    std::vector<std::string> no_victim_zones;

    std::vector<std::string> multi_room_zones;

    std::string change_zone;

    std::string class_only_boundary;

    std::unordered_map<std::string,int> dist_from_change_zone;

    std::unordered_map<std::string,std::vector<std::string>> graph;

    // ******

    // *** General ***
    std::string team_comp;

    // ******

    //*** agents ***

    std::unordered_map<std::string,std::string> role;

    std::unordered_map<std::string,std::string> agent_loc;

    std::unordered_map<std::string,bool> holding;

    std::unordered_map<std::string,int> time;

    std::unordered_map<std::string,std::string> picked_up_from;

    // ******

    //*** areas ***

    std::unordered_map<std::string,int> blocks_broken;

    std::unordered_map<std::string,bool> r_triaged_here;

    std::unordered_map<std::string,bool> c_triaged_here;

    std::unordered_map<std::string,bool> c_awake;

    std::unordered_map<std::string,int> picked_up_here;

    std::unordered_map<std::string,int> dropped_off_here;

    // ******

    // *** score ***

    int c_triage_total;
    int r_triage_total;

    int c_max;
    int r_max;

    // ******

    // *** (agent,area) ***
    std::unordered_map<std::string,std::unordered_map<std::string, int>> visited; 

    std::unordered_map<std::string,std::unordered_map<std::string, bool>> marked_area_1;

    std::unordered_map<std::string,std::unordered_map<std::string, bool>> marked_area_2;

    std::unordered_map<std::string,std::unordered_map<std::string, bool>> marked_area_3;
 
    // ******
    
    // *** (area_1,area_2) ***
    std::unordered_map<std::string,std::unordered_map<std::string,bool>> adjacent; 

    // ******

    // *** (agent, area_picked_up, area_dropped_off) ***
    std::unordered_map<std::string,std::unordered_map<std::string, std::unordered_map<std::string, int>>> vic_relocations;
    
    // ******

    // *** (agent, area_placed, area_marked) ***
    std::unordered_map<std::string,std::unordered_map<std::string, std::unordered_map<std::string, bool>>> marked_opening_1;

    std::unordered_map<std::string,std::unordered_map<std::string, std::unordered_map<std::string, bool>>> marked_opening_2;

    std::unordered_map<std::string,std::unordered_map<std::string, std::unordered_map<std::string, bool>>> marked_opening_3;

    // ******

   
    // Not part of the state representation!
    std::unordered_map<std::string,std::vector<Action>> action_tracker;
    std::unordered_map<std::string,std::vector<std::string>> loc_tracker;
    int seed = 100;

    nlohmann::json to_json() {
      return nlohmann::json{{"agents", this->agents},
               {"zones",this->zones},
               {"rooms",this->rooms},
               {"no_victim_zones",this->no_victim_zones},
               {"multi_room_zones",this->multi_room_zones},
               {"change_zone",this->change_zone},
               {"role",this->role},
               {"agent_loc",this->agent_loc},
               {"holding",this->holding},
               {"blocks_broken",this->blocks_broken},
               {"r_triaged_here",this->r_triaged_here},
               {"c_triaged_here",this->c_triaged_here},
               {"c_triage_total",this->c_triage_total},
               {"r_triage_total",this->r_triage_total},
               {"c_max", this->c_max},
               {"r_max",this->r_max},
               {"c_awake",this->c_awake},
               {"time",this->time},
               {"visited",this->visited},
               {"marked_area_1", this->marked_area_1},
               {"marked_area_2", this->marked_area_2},
               {"marked_area_3", this->marked_area_3},
               {"marked_opening_1", this->marked_opening_1},
               {"marked_opening_2", this->marked_opening_2},
               {"marked_opening_3", this->marked_opening_3}};
    }
};

class TeamSARSelector {
  public:
    double mean = 0.0;
    int sims = 0;

    double selectFunc(int pSims, double c, int r_l, int r_t) {
      return this->mean + ((c*r_l)/r_t)*sqrt(log(pSims)/this->sims);
    }

    double rewardFunc(TeamSARState s) {
      return (50.00*s.c_triage_total + 10.00*s.r_triage_total)/(50.00*s.c_max + 10.00*s.r_max);
    }

};

class TeamSARDomain {
  public:
    Operators<TeamSARState> operators = 
      Operators<TeamSARState>({{"!triageReg",triageReg},
                           {"!triageCrit",triageCrit},
                           {"!wakeCrit",wakeCrit},
                           {"!break_block",break_block},
                           {"!pickup_vic",pickup_vic},
                           {"!put_down_vic",put_down_vic},
                           {"!change_to_Medical_Specialist",change_to_Medical_Specialist},
                           {"!change_to_Hazardous_Material_Specialist",change_to_Hazardous_Material_Specialist},
                           {"!change_to_Search_Specialist",change_to_Search_Specialist},
                           {"!mark_opening_1",mark_opening_1},
                           {"!mark_opening_2",mark_opening_2},
                           {"!mark_opening_3",mark_opening_3},
                           {"!mark_area_1",mark_area_1},
                           {"!mark_area_2",mark_area_2},
                           {"!mark_area_3",mark_area_3},
                           {"!move",move},
                           {"!exit",exit}});

    pOperators<TeamSARState> poperators = 
      pOperators<TeamSARState>({{"!triageReg",triageReg},
                           {"!triageCrit",triageCrit},
                           {"!wakeCrit",wakeCrit},
                           {"!break_block",break_block},
                           {"!pickup_vic",pickup_vic},
                           {"!put_down_vic",put_down_vic},
                           {"!change_to_Medical_Specialist",change_to_Medical_Specialist},
                           {"!change_to_Hazardous_Material_Specialist",change_to_Hazardous_Material_Specialist},
                           {"!change_to_Search_Specialist",change_to_Search_Specialist},
                           {"!mark_opening_1",mark_opening_1},
                           {"!mark_opening_2",mark_opening_2},
                           {"!mark_opening_3",mark_opening_3},
                           {"!mark_area_1",mark_area_1},
                           {"!mark_area_2",mark_area_2},
                           {"!mark_area_3",mark_area_3},
                           {"!move",move},
                           {"!exit",exit}});


    cMethods<TeamSARState> cmethods =
      cMethods<TeamSARState>({{"SAR",
                          {SAR}},
                         {"Do_mission",
                          {no_class,
                           h,
                           m,
                           s,
                           hh,
                           hm,
                           hs,
                           mm,
                           ms,
                           ss,
                           hhh,
                           hhm,
                           hhs,
                           hmm,
                           hms,
                           hss,
                           mmm,
                           mms,
                           mss,
                           sss,
                           out_of_time}},
                         {"No_class",
                          {single_agent_no_class,
                           comp_change,
                           out_of_time}},
                         {"H",
                          {single_agent_h,
                           comp_change,
                           out_of_time}},
                         {"M",
                          {single_agent_m,
                           comp_change,
                           out_of_time}},
                         {"S",
                          {single_agent_s,
                           comp_change,
                           out_of_time}},
                         {"HH",
                          {single_agent_hh,
                           comp_change,
                           out_of_time}},
                         {"HM",
                          {single_agent_hm,
                           comp_change,
                           out_of_time}},
                         {"HS",
                          {single_agent_hs,
                           comp_change,
                           out_of_time}},
                         {"MM",
                          {single_agent_mm,
                           comp_change,
                           out_of_time}},
                         {"MS",
                          {single_agent_ms,
                           comp_change,
                           out_of_time}},
                         {"SS",
                          {single_agent_ss,
                           comp_change,
                           out_of_time}},
                         {"HHH",
                          {single_agent_hhh,
                           comp_change,
                           out_of_time}},
                         {"HHM",
                          {single_agent_hhm,
                           group_hhm,
                           comp_change,
                           out_of_time}},
                         {"HHS",
                          {single_agent_hhs,
                           comp_change,
                           out_of_time}},
                         {"HMM",
                          {single_agent_hmm,
                           group_hmm,
                           comp_change,
                           out_of_time}},
                         {"HMS",
                          {single_agent_hms,
                           group_hms,
                           comp_change,
                           out_of_time}},
                         {"HSS",
                          {single_agent_hss,
                           comp_change,
                           out_of_time}},
                         {"MMM",
                          {single_agent_mmm,
                           group_mmm,
                           comp_change,
                           out_of_time}},
                         {"MMS",
                          {single_agent_mms,
                           group_mms,
                           comp_change,
                           out_of_time}},
                         {"MSS",
                          {single_agent_mss,
                           group_mss,
                           comp_change,
                           out_of_time}},
                         {"SSS",
                          {single_agent_sss,
                           comp_change,
                           out_of_time}},
                         {"Assign_agent_for_task",
                          {agent1_task,
                           agent2_task,
                           agent3_task}},
                         {"Agent_1_task",
                          {no_class_task,
                           h_task,
                           m_task,
                           s_task}},
                         {"Agent_2_task",
                          {no_class_task,
                           h_task,
                           m_task,
                           s_task}},
                         {"Agent_3_task",
                          {no_class_task,
                           h_task,
                           m_task,
                           s_task}},
                         {"No_class_task",
                          {move_agent}},
                         {"H_task",
                          {move_agent,
                           clear_area}},
                         {"Clear_area",
                          {break_blocks,
                           done_breaking}},
                         {"M_task",
                          {move_agent,
                           triage_regs_in_area,
                           triage_critical}},
                         {"Triage_regs_in_area",
                          {triage_regs,
                           done_triaging}},
                         {"S_task",
                          {move_agent,
                           relocate_victim,
                           resume_relocate_victim}},
                         {"Relocate_vic",
                          {pickup_victim,
                           move_victim,
                           putdown_victim,
                           need_to_do_something_else,
                           no_time_to_putdown}},
                         {"Assign_agents_for_group_task",
                          {all_task}},
                         {"All_task",
                          {wake_crit_vic}},
                         {"Team_composition_change",
                          {agent1_change_role,
                           agent2_change_role,
                           agent3_change_role}},
                         {"Agent_1_change_role",
                          {changing_role}},
                         {"Agent_2_change_role",
                          {changing_role}},
                         {"Agent_3_change_role",
                          {changing_role}},
                         {"Changing_role",
                          {moving_to_change_zone,
                           picking_role,
                           no_time_to_change}},
                         {"Pick_new_role",
                          {choose_Medical_Specialist,
                           choose_Hazardous_Material_Specialist,
                           choose_Search_Specialist}}});

    TeamSARDomain() {
      std::cout << "Operators: ";
      print(this->operators);

      std::cout << "Method: ";
      print(this->cmethods);
    };
};
