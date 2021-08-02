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
sample_loc(std::vector<std::string> zones,
           std::unordered_map<std::string, int> visited,
           int seed) {
  std::vector<double> w;
  for (auto a : zones) {
    if (visited.find(a) == visited.end()) {
      w.push_back(1.0);
    }
    else {
      w.push_back(1.0/(1.0 + visited[a]));
    }
  }
  std::mt19937 gen(seed);
  std::discrete_distribution<int> dist (w.begin(),w.end());
  int s = dist(gen);
  return zones[s];
}

std::string 
sample_loc(std::vector<std::string> zones,
           std::unordered_map<std::string, int> visited) {
  std::vector<double> w;
  for (auto a : zones) {
    if (visited.find(a) == visited.end()) {
      w.push_back(1.0);
    }
    else {
      w.push_back(1.0/(1.0 + visited[a]));
    }
  }
  std::random_device rd;
  std::mt19937 gen(rd());
  std::discrete_distribution<int> dist (w.begin(),w.end());
  int s = dist(gen);
  return zones[s];
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    state.time[agent] = end;
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    state.time[agent] = end;
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
    }

    return state;
  }
  return std::nullopt;
}

template <class State> double put_down_vic(State pre_state, State post_state, Args args) {
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
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
    if (!state.action_tracker.empty()) {
      state.action_tracker.pop_back();
    }

    return state;
}

template <class State> double exit(State pre_state, State post_state, Args args) {
    return 1;
}

// Methods
template <class State> pTasks SAR(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  return {1.0,
    {Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}), {"agent1","agent2","agent3"}),
     Task("!exit", Args({{"agent",agent1},{"start","900"},{"duration","0"}}), {"agent","start","duration"}),
     Task("!exit", Args({{"agent",agent2},{"start","900"},{"duration","0"}}), {"agent","start","duration"}),
     Task("!exit", Args({{"agent",agent3},{"start","900"},{"duration","0"}}), {"agent","start","duration"})}};
}

template <class State> pTasks assign_tasks(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  auto min_agent = agent1;
  if (state.action_tracker.empty()) {
    auto min_time = state.time[agent1];
    for (auto a : state.agents) {
      if (state.time[a] < min_time) {
        min_agent = a;
        min_time = state.time[a];
      }
    }
  }
  else {
    Action act = state.action_tracker.back();
    if (act.agent == "all" || act.action == "!exit") {
      return {0,{}};
    }
    min_agent = act.agent;
  }

  if (state.time[min_agent] < 900) {
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
    bool can_wake_here = true;
    bool have_Medical_Specialist = false;
    for (auto a : state.agents) {
      if (state.role[a] == "Medical_Specialist") {
        have_Medical_Specialist = true;
      }
      if (state.agent_loc[a] != c_vic_area) {
        can_wake_here = false;
      } 
    }
    double prob = 1;

    bool r_triaged_here;
    if(state.r_triaged_here.find(c_vic_area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[c_vic_area];
    }

    if (can_wake_here && have_Medical_Specialist) {
      if (in_room && r_triaged_here) {
        prob = 0.99;
      }
      else {
        prob = 0.01;
      }
    }
    return {prob,
          {Task("Do_task", Args({{"agent",min_agent}}),{"agent"}),
           Task("Explore", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}), {"agent1","agent2","agent3"})}};
  }
  return {0,{}};
}

template <class State> pTasks wake_crit_vic(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  auto min_agent = agent1;
  std::string duration = "1";
  int start_num = std::max({state.time[agent1],state.time[agent2],state.time[agent3]});
  std::string start = std::to_string(start_num);
  if (state.action_tracker.empty()) {
    auto min_time = state.time[agent1];
    for (auto a : state.agents) {
      if (state.time[a] < min_time) {
        min_agent = a;
        min_time = state.time[a];
      }
    }
  }
  else { 
    Action act = state.action_tracker.back();
    if (act.agent != "all") {
      return {0,{}};
    }
    min_agent = act.agent;
    duration = act.duration;
    start = act.start;
  }

  if (state.time[min_agent] < 900 && !in(state.agent_loc[min_agent],state.no_victim_zones)) {
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
    bool can_wake_here = true;
    bool have_Medical_Specialist = false;
    for (auto a : state.agents) {
      if (state.role[a] == "Medical_Specialist") {
        have_Medical_Specialist = true;
      }
      if (state.agent_loc[a] != c_vic_area) {
        can_wake_here = false;
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

    if (can_wake_here && have_Medical_Specialist) {
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
                                     {"agent1",agent1}}), {"agent1","agent2","agent3","area","start","duration"}),
           Task("Explore", Args({{"agent3",agent3},{"agent2",agent2},{"agent1",agent1}}),{"agent1","agent2","agent3"})}};
  }
  return {0,{}};
}

template <class State> pTasks out_of_time(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];

  auto min_agent = agent1;
  if (state.action_tracker.empty()) {
    auto min_time = state.time[agent1];
    for (auto a : state.agents) {
      if (state.time[a] < min_time) {
        min_agent = a;
        min_time = state.time[a];
      }
    }
  }
  else { 
    Action act = state.action_tracker.back();
    if (act.action == "!exit") {
      return {1,{}};
    }
    return {0,{}};
  }

  if (state.time[min_agent] >= 900) {
    return {1.0,{}};
  }
  return {0,{}};
}

template <class State> pTasks choose_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!change_to_Medical_Specialist") {
      return {0,{}};
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
                                     {"agent",agent}}), {"agent","start","duration"})}};
  }
  return {0,{}};

}

template <class State> pTasks choose_Hazardous_Material_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!change_to_Hazardous_Material_Specialist") {
      return {0,{}};
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
                                     {"agent",agent}}), {"agent","start","duration"})}};
  }
  return {0,{}};

}

template <class State> pTasks choose_Search_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!change_to_Search_Specialist") {
      return {0,{}};
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
                                     {"agent",agent}}),{"agent","start","duration"})}};
  }
  return {0,{}};

}

template <class State> pTasks no_class_change(State state,Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action.substr(0,11) != "!change_to_") {
      return {0,{}};
    }
  }

  if (state.role[agent] == "NONE" && state.time[agent] < 900 &&
      state.agent_loc[agent] == state.change_zone) {
    return {0.5,
      {Task("Change_role",Args({{"agent",agent}}),{"agent"})}};
  }
  return {0,{}};
}

template <class State> pTasks no_class_move(State state,Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!move") {
      return {0,{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "5";
    start = std::to_string(state.time[agent]);
  }


  if (state.role[agent] == "NONE" && state.time[agent] < 900) {
    double prob;
    if (state.agent_loc[agent] == state.change_zone) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      while (n_area == state.agent_loc[agent]) {
        n_area = sample_loc(state.zones,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    return {prob,
      {Task("!move",Args({{"duration",duration},
                            {"start",start},
                            {"n_area",n_area},
                            {"c_area",state.agent_loc[agent]},
                            {"agent",agent}}), {"agent","c_area","n_area","start","duration"})}};
  }
  return {0,{}};
}

template <class State> pTasks Medical_Specialist_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Medical_Specialist") {
    return {1.0,
      {Task("Do_Medical_Specialist_task", Args({{"agent", agent}}), {"agent"})}};
  }
  return {0,{}};

}

template <class State> pTasks Search_Specialist_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Search_Specialist") {
    return {1.0,
      {Task("Do_Search_Specialist_task", Args({{"agent", agent}}),{"agent"})}};
  }
  return {0,{}};

}

template <class State> pTasks Hazardous_Material_Specialist_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Hazardous_Material_Specialist") {
    return {1.0,
      {Task("Do_Hazardous_Material_Specialist_task", Args({{"agent", agent}}),{"agent"})}};
  }
  return {0,{}};

}

template <class State> pTasks triageReg_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!triageReg") {
      return {0,{}};
    }
  }
  if (state.role[agent] == "Medical_Specialist" && state.time[agent] < 900 &&
      !in(state.agent_loc[agent],state.no_victim_zones) &&
      state.r_triage_total < state.r_max) {
    double prob;

    bool c_awake;
    if(state.c_awake.find(state.agent_loc[agent]) == state.c_awake.end()) {
      c_awake = false;
    }
    else {
      c_awake = state.c_awake[state.agent_loc[agent]];
    }

    if (in(state.agent_loc[agent],state.rooms) && c_awake) {
      prob = 0.01;
    }
    else {
      prob = 13.0/173;
    }
    return {prob,
      {Task("Triage_area",Args({{"area",state.agent_loc[agent]},
                            {"agent",agent}}), {"agent","area"})}};
  }  
  return {0,{}};
}

template <class State> pTasks triageCrit_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!triageCrit") {
      return {0,{}};
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
    double prob;
    if (in(state.agent_loc[agent],state.rooms)) {
      if (state.r_triage_total < state.r_max) {
        prob = (1.0/3) - 0.01;
      }
      else {
        prob = 1.0/3;
      }
    }
    else {
      prob = 1.0/173;
    }
    return {prob,
      {Task("!triageCrit",Args({{"duration",duration},
                                {"start",start},
                                {"area",state.agent_loc[agent]},
                                {"agent",agent}}), {"agent","area","start","duration"})}};
  }  
  return {0,{}};
}

template <class State> pTasks move_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!move") {
      return {0,{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "6";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Medical_Specialist" && state.time[agent] < 900) {
    double prob;
    if (in(state.agent_loc[agent],state.no_victim_zones)) {
      if (state.agent_loc[agent] == state.change_zone) {
        prob = 8.0/19;
      }
      else {
        prob = 1.0;
      }
    }
    else {

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

      if (in(state.agent_loc[agent],state.rooms) && c_awake) {
        if (c_triaged_here) {
          prob = 0.99;
          if (state.r_triage_total >= state.r_max) {
            prob = 1;
          }
        }
        else {
          prob = 2.0/3;
          if (state.c_triage_total >= state.c_max) {
            prob = 0.99;
            if (state.r_triage_total >= state.r_max) {
              prob = 1;
            }
          }
        }
      }
      else {
        prob = 159.0/173;
        if (state.c_triage_total >= state.c_max) {
          prob = 160.0/173;
        }

        if (state.r_triage_total >= state.r_max) {
          prob = 172.0/173;
        }
      }
      if (state.r_triage_total >= state.r_max && state.c_triage_total >= state.c_max) {
        prob = 1.0;
      }
    }

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      while (n_area == state.agent_loc[agent]) {
        n_area = sample_loc(state.zones,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    return {prob,
      {Task("!move",Args({{"duration",duration},
                            {"start",start},
                            {"n_area",n_area},
                            {"c_area",state.agent_loc[agent]},
                            {"agent",agent}}), {"agent","c_area","n_area","start","duration"})}};
  }  
  return {0,{}};
}

template <class State> pTasks change_Medical_Specialist(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action.substr(0,11) != "!change_to_") {
      return {0,{}};
    }
  }
 
  if (state.role[agent] == "Medical_Specialist" && 
      state.agent_loc[agent] == state.change_zone &&
      state.time[agent] < 900) {

    return {11.0/19,
      {Task("Change_role",Args({{"agent",agent}}), {"agent"})}};
  }  
  return {0,{}};
}

template <class State> pTasks triageArea(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!triageReg") {
      return {0,{}};
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
    double prob;

    bool r_triaged_here;
    if(state.r_triaged_here.find(area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[area];
    }

    if (r_triaged_here) {
      prob = 13.0/24;
    }
    else {
      prob = 1.0;
    }
    return {prob,
      {Task("!triageReg",Args({{"duration",duration},
                                {"start",start},
                                {"area",area},
                                {"agent",agent}}),{"agent","area","start","duration"}),
       Task("Triage_area",Args({{"area",area},
                                {"agent",agent}}),{"agent","area"})}};
  }  
  return {0,{}};
}

template <class State> pTasks doneTriaging(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];

  if (state.role[agent] == "Medical_Specialist") {
    double prob;

    bool r_triaged_here;
    if(state.r_triaged_here.find(area) == state.r_triaged_here.end()) {
      r_triaged_here = false;
    }
    else {
      r_triaged_here = state.r_triaged_here[area];
    }

    if (r_triaged_here) {
      prob = 11.0/24;
    }
    else {
      prob = 0;
    }
    if (state.time[agent] >= 900) {
      prob = 1;
    }

    return {prob,{}};
  }  
  return {0,{}};
}

template <class State> pTasks clear_blocks_Hazardous_Material_Specialist(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!break_block") {
      return {0,{}};
    }
  }

  if (state.role[agent] == "Hazardous_Material_Specialist" && 
      state.time[agent] < 900 && !in(state.agent_loc[agent],state.no_victim_zones)) {
    return {18.0/66,
      {Task("Clear_area",Args({{"area",state.agent_loc[agent]},
                                      {"agent",agent}}),{"agent","area"})}};
  }  
  return {0,{}};
}

template <class State> pTasks clearArea(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!break_block") {
      return {0,{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "1";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Hazardous_Material_Specialist" && state.time[agent] < 900) {
    double prob;

    bool blocks_broken;
    if(state.blocks_broken.find(area) == state.blocks_broken.end()) {
      blocks_broken = false;
    }
    else {
      blocks_broken = state.blocks_broken[area];
    }

    if (blocks_broken > 0) {
      prob = 91.0/108;
    }
    else {
      prob = 1.0;
    }

    return {prob,
      {Task("!break_block",Args({{"duration",duration},
                            {"start",start},
                            {"area",area},
                            {"agent",agent}}),{"agent","area","start","duration"}),
       Task("Clear_area",Args({{"area",area},
                               {"agent",agent}}),{"agent","area"})}};
  }  
  return {0,{}};
}

template <class State> pTasks doneBreaking(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.role[agent] == "Hazardous_Material_Specialist") {
    double prob;

    bool blocks_broken;
    if(state.blocks_broken.find(area) == state.blocks_broken.end()) {
      blocks_broken = false;
    }
    else {
      blocks_broken = state.blocks_broken[area];
    }

    if (blocks_broken > 0) {
      prob = 17.0/108;
    }
    else {
      prob = 0;
    }
    if (state.time[agent] >= 900) {
      prob = 1;
    }

    return {prob,{}};
  }  
  return {0,{}};
}

template <class State> pTasks move_Hazardous_Material_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!move") {
      return {0,{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "8";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Hazardous_Material_Specialist" && state.time[agent] < 900) {
    double prob;
    if (in(state.agent_loc[agent],state.no_victim_zones)) {
      if (state.agent_loc[agent] == state.change_zone) {
        prob = 3.0/5;
      }
      else {
        prob = 1.0;
      }
    }
    else {
      prob = 48.0/66;
    }

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      while (n_area == state.agent_loc[agent]) {
        n_area = sample_loc(state.zones,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    return {prob,
      {Task("!move",Args({{"duration",duration},
                          {"start",start},
                          {"n_area",n_area},
                          {"c_area",state.agent_loc[agent]},
                          {"agent",agent}}),{"agent","c_area","n_area","start","duration"})}};
  }  
  return {0,{}};
}

template <class State> pTasks change_Hazardous_Material_Specialist(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action.substr(0,11) != "!change_to_") {
      return {0,{}};
    }
  }
 
  if (state.role[agent] == "Hazardous_Material_Specialist" && 
      state.agent_loc[agent] == state.change_zone &&
      state.time[agent] < 900) {

    return {2.0/5,
      {Task("Change_role",Args({{"agent",agent}}), {"agent"})}};
  }  
  return {0,{}};
}

template <class State> pTasks relocate_victim_Search_Specialist(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!pickup_vic") {
      return {0,{}};
    }
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900 &&
      !in(state.agent_loc[agent],state.no_victim_zones) &&
      state.r_triage_total < state.r_max) {

    return {6.0/161,
      {Task("Relocate_vic",Args({{"agent",agent}}),{"agent"})}};
  }  
  return {0,{}};
}

template <class State> pTasks pickup_victim(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!pickup_vic") {
      return {0,{}};
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

    return {1.0,
      {Task("!pickup_vic",Args({{"duration",duration},
                                {"start",start},
                                {"area",state.agent_loc[agent]},
                                {"agent",agent}}),{"agent","area","start","duration"}),
       Task("Relocate_vic",Args({{"agent",agent}}), {"agent"})}};
  }  
  return {0,{}};
}

template <class State> pTasks move_victim(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!move") {
      return {0,{}};
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

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      while (n_area == state.agent_loc[agent]) {
        n_area = sample_loc(state.zones,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    return {6.0/12,
      {Task("!move",Args({{"duration",duration},
                          {"start",start},
                          {"n_area",n_area},
                          {"c_area",state.agent_loc[agent]},
                          {"agent",agent}}),{"agent","c_area","n_area","start","duration"}),
       Task("Relocate_vic",Args({{"agent",agent}}),{"agent"})}};
  }  
  return {0,{}};
}

template <class State> pTasks putdown_victim(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!put_down_vic") {
      return {0,{}};
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

    return {6.0/12,
      {Task("!put_down_vic",Args({{"duration",duration},
                                {"start",start},
                                {"area",state.agent_loc[agent]},
                                {"agent",agent}}),{"agent","area","start","duration"})}};
  }  
  return {0,{}};
}

template <class State> pTasks no_time_to_putdown(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "Search_Specialist" && state.time[agent] >= 900 &&
      state.holding[agent]) {

    return {1.0,{}};
  }  
  return {0,{}};
}

template <class State> pTasks move_Search_Specialist(State state, Args args) {
  auto agent = args["agent"];

  std::string duration;
  std::string start;
  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action != "!move") {
      return {0,{}};
    }
    duration = act.duration;
    start = act.start;
  }
  else {
    duration = "4";
    start = std::to_string(state.time[agent]);
  }

  if (state.role[agent] == "Search_Specialist" && state.time[agent] < 900) {
    double prob;
    if (in(state.agent_loc[agent],state.no_victim_zones)) {
      if (state.agent_loc[agent] == state.change_zone) {
        prob = 2.0/6; 
      }
      else {
        prob = 1.0;
      }
    }
    else {
      if (state.r_triage_total < state.r_max) {
        prob = 155.0/161;
      }
      else {
        prob = 1.0;
      }
    }

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      while (n_area == state.agent_loc[agent]) {
        n_area = sample_loc(state.zones,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    return {prob,
      {Task("!move",Args({{"duration",duration},
                          {"start",start},
                          {"n_area",n_area},
                          {"c_area",state.agent_loc[agent]},
                          {"agent",agent}}),{"agent","c_area","n_area","start","duration"})}};
  }  
  return {0,{}};
}

template <class State> pTasks change_Search_Specialist(State state, Args args) {
  auto agent = args["agent"];

  if (!state.action_tracker.empty()) {
    Action act = state.action_tracker.back();
    if (act.action.substr(0,11) != "!change_to_") {
      return {0,{}};
    }
  }
 
  if (state.role[agent] == "Search_Specialist" && 
      state.agent_loc[agent] == state.change_zone &&
      state.time[agent] < 900) {

    return {4.0/6,
      {Task("Change_role",Args({{"agent",agent}}),{"agent"})}};
  }  
  return {0,{}};
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

    // ******

    //*** agents ***

    std::unordered_map<std::string, std::string> role;

    std::unordered_map<std::string, std::string> agent_loc;

    std::unordered_map<std::string,bool> holding;

    std::unordered_map<std::string, int> time;

    // ******

    //*** areas ***

    std::unordered_map<std::string,int> blocks_broken;

    std::unordered_map<std::string,bool> r_triaged_here;

    std::unordered_map<std::string,bool> c_triaged_here;

    std::unordered_map<std::string, bool> c_awake;

    // ******

    // *** score ***

    int c_triage_total;
    int r_triage_total;

    int c_max;
    int r_max;

    // ******

    // (agent,area)
    std::unordered_map<std::string, std::unordered_map<std::string, int>> visited; 
    
    // Not part of the state representation!
    std::vector<Action> action_tracker;
    std::unordered_map<std::string, std::vector<std::string>> loc_tracker;
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
               {"visited",this->visited}};
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
                           {"!move",move},
                           {"!exit",exit}});


    Methods<TeamSARState> methods =
      Methods<TeamSARState>({{"SAR",
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
                           no_time_to_putdown}}});

    TeamSARDomain() {
      std::cout << "Operators: ";
      print(this->operators);

      std::cout << "Method: ";
      print(this->methods);
    };
};
