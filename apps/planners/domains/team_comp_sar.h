#include "cpphop.h"
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
           int def = 1.0) {
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
           int def = 1.0) {
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

template <class State> std::string get_team_code(State state) {
  std::string team_code = "";
  for (auto a : state.agents) {
    if(state.role[a] != "NONE") {
      if (state.role[a] == "Medical_Specialist") {
        team_code += "m";
      }
      if (state.role[a] == "Hazardous_Material_Specialist") {
        team_code += "h";
      }
      if (state.role[a] == "Search_Specialist") {
        team_code += "s";
      }
    }
  } 
  sort(team_code.begin(),team_code.end());

  return team_code;
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
    state.team_code = get_team_code(state);
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
    state.team_code = get_team_code(state);
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
    state.team_code = get_team_code(state);
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
  if (state.team_code.empty()) {
    return {"no_class_0",
      {Task("No_class", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.action.substr(0,11) == "!change_to_") {
        role_change = true;
      }
    }
  }
  
  if (act_available) {
    if (!role_change) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    std::string cond = "comp_change_0";
    if (state.team_comp.size() <= 1) {
      cond = "comp_change_1";
    }
    return {cond,
          {Task("Team_composition_change", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("Do_mission", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks h(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "h") {
    return {"h_0",
      {Task("H", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "m") {
    return {"m_0",
      {Task("M", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "s") {
    return {"s_0",
      {Task("S", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "hh") {
    return {"hh_0",
      {Task("HH", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "hm") {
    return {"hm_0",
      {Task("HM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "hs") {
    return {"hs_0",
      {Task("HS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "mm") {
    return {"mm_0",
      {Task("MM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "ms") {
    return {"ms_0",
      {Task("MS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "ss") {
    return {"ss_0",
      {Task("SS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "hhh") {
    return {"hhh_0",
      {Task("HHH", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "hhm") {
    return {"hhm_0",
      {Task("HHM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    return {"group_hhm_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HHM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hhs(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "hhs") {
    return {"hhs_0",
      {Task("HHS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "hmm") {
    return {"hmm_0",
      {Task("HMM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    return {"group_hmm_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HMM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "hms") {
    return {"hms_0",
      {Task("HMS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    return {"group_hms_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("HMS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks hss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "hss") {
    return {"hss_0",
      {Task("HSS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  if (state.team_code == "mmm") {
    return {"mmm_0",
      {Task("MMM", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    return {"group_mmm_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MMM", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}


template <class State> cTasks mms(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "mms") {
    return {"mms_0",
      {Task("MMS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    return {"group_mms_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MMS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks mss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "mss") {
    return {"mss_0",
      {Task("MSS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
  if (min_time < 900) {
    return {"group_mss_0",
          {Task("Assign_agents_for_group_task", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}),{"agent1","agent2","agent3"},{agent1,agent2,agent3}),
           Task("MSS", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks sss(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.team_code == "sss") {
    return {"sss_0",
      {Task("SSS", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"},{agent1,agent2,agent3})}};
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
    if (!single_agent_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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

  bool group_task = false;
  bool act_available = false;
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.agent != a) {
        group_task = true;
      }
    }
  }
  
  if (act_available) {
    if (!group_task) {
      return {"NIL",{}};
    }
  }

  int min_time = std::min(state.time[agent1], state.time[agent2], state.time[agent3]);
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
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

  if (state.time[agent1] < 900) {
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
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

  if (state.time[agent2] < 900) {
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
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

  if (state.time[agent3] < 900) {
    return {"U",
          {Task("Agent_3_task", Args({{"agent",agent3}}),{"agent"},{agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks no_class_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "None") {
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

template <class State> cTasks m_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Medical_Specialist") {
    return {"m_task_0",
          {Task("M_task", Args({{"agent",agent}}),{"agent"},{agent})}};
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
      n_area = sample_loc(state.graph[state.agent_loc[agent]],state.visited[agent],state.seed);
      state.seed++;
  }
  else {
    n_area = state.loc_tracker[agent].back();
  }

  if (state.time[agent] < 900) {
    std::string cond = "move_agent_0";
    if (state.team_comp >= 3) {
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

    return {prob,
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.action.substr(0,11) == "!change_to_") {
        change_role = true;
      }
    }
  }
  
  if (act_available) {
    if (!change_role) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent1] < 900) {
    return {1.0/3,
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.action.substr(0,11) == "!change_to_") {
        change_role = true;
      }
    }
  }
  
  if (act_available) {
    if (!change_role) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent2] < 900) {
    return {1.0/3,
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
  for (auto a : state.agents) {
    if (!state.action_tracker[a].empty()) {
      act_available = true;
      auto act = state.action_tracker[a].back();
      if (act.action.substr(0,11) == "!change_to_") {
        change_role = true;
      }
    }
  }
  
  if (act_available) {
    if (!change_role) {
      return {"NIL",{}};
    }
  }

  if (state.time[agent3] < 900) {
    return {1.0/3,
          {Task("Agent_3_change_role", Args({{"agent",agent3}}),{"agent"},{agent3})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks changing_role(State state, Args args) {
  auto agent = args["agent"];

  if (state.time[agent] < 900) {
    return {1.0,
          {Task("Changing_role", Args({{"agent",agent}}),{"agent"},{agent})}};
  }
  return {"NIL",{}};
}

template <class State> cTasks moving_to_change_zone(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker[agent].empty()) {
    auto act = state.action_tracker[a].back();
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
    return {1.0,
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

template <class State> cTasks Picking_role(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker[agent].empty()) {
    auto act = state.action_tracker[a].back();
    if (act.action.substr(0,11) != "!change_to_") {
      return {"NIL",{}};
    } 
  }

  if (state.time[agent] < 900 && state.agent_loc[agent] == state.change_zone) {
    return {1.0,
          {Task("Pick_new_role", Args({{"agent",agent}}),{"agent"},{agent})}};
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


  if (state.time[agent1] < 900) {
    return {1.0,
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
      state.team_comp.size() >= 3 && state.team_comp.contains("m")) {
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
    double prob = 0;

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (all_gathered) {
      if (in_room && r_triaged_here) {
        prob = 0.01;
      }
      else {
        prob = 0.99;
      }
    }
 
    return {prob,
          {Task("!wakeCrit", Args({{"duration",duration},
                                     {"start",start},
                                     {"area",state.agent_loc[min_agent]},
                                     {"agent3",agent3},
                                     {"agent2",agent2},
                                     {"agent1",agent1}}), {"agent1","agent2","agent3","area","start","duration"},{agent1,agent2,agent3})}}
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
      return {1,{}};
    }
    return {"NIL",{}};
  }

  if (state.time[min_agent] >= 900) {
    return {1.0,{}};
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
    return {4.0/11,
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
    return {3.0/11,
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
    return {4.0/11,
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

    std::unordered_map<std::string,int> dist_from_change_zone;

    std::unordered_map<std::string,std::vector<std::string>> graph;

    // ******

    // *** General ***
    std::string team_code;

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
    double mean = 0;
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


    cMethods<TeamSARState> methods =
      cMethods<TeamSARState>({{"SAR",
                          {SAR}},
                         {"Change_role",
                          {choose_Medical_Specialist,
                           choose_Hazardous_Material_Specialist,
                           choose_Search_Specialist}},
                         {"Explore",
                          {assign_tasks,
                           wake_crit_vic,
                           out_of_time}},
                         {"Do_task",
                          {no_class_change,
                           no_class_move,
                           Medical_Specialist_task,
                           Search_Specialist_task,
                           Hazardous_Material_Specialist_task}},
                         {"Do_Medical_Specialist_task",
                          {triageReg_Medical_Specialist,
                           triageCrit_Medical_Specialist,
                           move_Medical_Specialist,
                           change_Medical_Specialist}},
                         {"Do_Hazardous_Material_Specialist_task",
                          {clear_blocks_Hazardous_Material_Specialist,
                           move_Hazardous_Material_Specialist,
                           change_Hazardous_Material_Specialist}},
                         {"Do_Search_Specialist_task",
                          {relocate_victim_Search_Specialist,
                           resume_relocate_victim_Search_Specialist,
                           move_Search_Specialist,
                           change_Search_Specialist}},
                         {"Triage_area",
                          {triageArea,
                           doneTriaging}},
                         {"Clear_area",
                          {clearArea,
                           doneBreaking}},
                         {"Relocate_vic",
                          {pickup_victim,
                           move_victim,
                           putdown_victim,
                           need_to_do_something_else,
                           no_time_to_putdown}}});

    TeamSARDomain() {
      std::cout << "Operators: ";
      print(this->operators);

      std::cout << "Method: ";
      print(this->methods);
    };
};
