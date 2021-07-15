#include "cpphop.h"
#include <math.h>
#include <nlohmann/json.hpp>
#include <string>
#include <algorithm>

// aux functions
std::string 
sample_loc(std::vector<std::string> rooms,
           std::unordered_map<std::string, int> visited,
           int seed) {
  std::vector<double> w;
  for (auto a : rooms) {
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
  return rooms[s];
}

std::unordered_map<std::string,std::vector<std::string>>
get_loc_seq(nlohmann::json j,
            std::vector<std::string> left_r,
            std::vector<std::string> right_r,
            std::vector<std::string> mid_r) {
  std::unordered_map<std::string,std::vector<std::string>> locs;
  std::vector<std::string> left = {};
  std::vector<std::string> right = {};
  std::vector<std::string> mid = {};
  for (auto& e : j) {
    std::string str = e["task"];
    if (str.substr(1,5) == "!move") {
      std::string n_area = str.substr(7,str.find(",",7) - 7);
      if (in(n_area,left_r)) {
        left.push_back(n_area);
      }
      if (in(n_area,right_r)) {
        right.push_back(n_area);
      }
      if (in(n_area,mid_r)) {
        mid.push_back(n_area);
      }
    }
  }
  std::reverse(left.begin(),left.end());
  std::reverse(right.begin(),right.end());
  std::reverse(mid.begin(),mid.end());
  locs["left"] = left;
  locs["right"] = right;
  locs["mid"] = mid;
  return locs;
}

std::string 
sample_loc(std::vector<std::string> rooms,
           std::unordered_map<std::string, int> visited) {
  std::vector<double> w;
  for (auto a : rooms) {
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
  return rooms[s];
}

// operators
template <class State> std::optional<State> search(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  int start = std::stoi(args["start"],nullptr);
  int duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.agent_loc[agent] == area && end <= 900) {
    
    state.write_time[agent] = end;
    state.write_times_searched[agent] = end;

    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    if (state.c_triage_total != state.c_max) {
      for (auto c : state.c_vic_loc[area]) {
        if (!in(c,state.c_seen[agent]) && !state.obs[c]) {
          state.c_seen[agent].push_back(c);
          state.time[agent] = end;

          state.times_searched[agent]++;

          state.write_c_seen[agent] = end;

          state.read_c_seen[agent] = std::max(state.read_c_seen[agent],end);
          return state;
        }
      }
    }


    if (state.r_triage_total != state.r_max) { 
      for (auto r : state.r_vic_loc[area]) {
        if (!in(r,state.r_seen[agent]) && !state.obs[r]) {
          state.r_seen[agent].push_back(r);
          state.write_r_seen[agent] = end;
          state.read_r_seen[agent] = std::max(state.read_r_seen[agent],end);
          break;
        }
      }
    }
    state.time[agent] = end;

    state.times_searched[agent]++;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double search(State pre_state, State post_state, Args args) {
  return 1.0;
}

template <class State> std::optional<State> triageReg(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  if (state.role[agent] == "medic" && state.agent_loc[agent] == area && 
      !state.r_seen[agent].empty() && end <= 900) {

    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_r_vic_loc[area] = end;
    state.write_r_triage_total = end;
    state.write_time[agent] = end;

    state.read_r_vic_loc[area] = std::max(state.read_r_vic_loc[area],end);
    state.read_r_triage_total = std::max(state.read_r_triage_total,end);
    
    std::string r = state.r_seen[agent].back();
    std::erase(state.r_vic_loc[area], r);
    for (auto a : state.agents) {
      std::erase(state.r_seen[a],r);
      state.read_r_seen[a] = std::max(state.read_r_seen[a],end);
      state.write_r_seen[a] = end;
    }
    state.r_triage_total = state.r_triage_total + 1; 
    state.time[agent] = end;
    return state;

  }
  else {
    return std::nullopt;
  }
}

template <class State> double triageReg(State pre_state,State post_state, Args args) {
  return 1;
}

template <class State> std::optional<State> wakeCrit(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  int a_count = 0;
  bool have_medic = false;
  int help_count = 0;
  for (auto a : state.agents) {
    state.read_agent_loc[a] = std::max(state.read_agent_loc[a],end);
    if (state.agent_loc[a] == area) {
      a_count++;
      state.read_role[a] = std::max(state.read_role[a],end); 
      state.read_c_seen[a] = std::max(state.read_c_seen[a],end);
      if (state.role[a] == "medic" && !state.c_seen[a].empty()) {
        have_medic = true;
      }
      state.read_help_wake[a] = std::max(state.read_help_wake[a],end);
      if (state.help_wake[a]) {
        help_count++;
      }
    }
  }

  if (state.agent_loc[agent] == area && a_count >= 3 && 
      have_medic && end <= 900) {
    
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_time[agent] = end;

    if (state.role[agent] != "medic") {
      state.write_help_wake[agent] = end;
      state.help_wake[agent] = true;
      state.time[agent] = end;;
      return state;
    }

    if (help_count >= 2) {
      for (auto a : state.agents) {
        state.write_help_wake[a] = end;
        state.help_wake[a] = false;
      } 
      
      std::string c = state.c_seen[agent].back();
      state.read_c_awake[c] = std::max(state.read_c_awake[c],end);
      state.write_c_awake[c] = end;
      state.c_awake[c] = true;
      state.time[agent] = end;
      return state;
    }
    return std::nullopt;
  }
  else {
    return std::nullopt;
  }
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

  std::string vic_awake = "NONE";
  for (auto c: state.c_seen[agent]) {
    state.read_c_awake[c] = std::max(state.read_c_awake[c],end);
    if (state.c_awake[c]) {
      vic_awake = c;
      break;
    }
  } 

  if (state.role[agent] == "medic" && vic_awake != "NONE" && 
      state.agent_loc[agent] == area && end <= 900) {

    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);
    state.read_c_vic_loc[area] = std::max(state.read_c_vic_loc[area],end);
    state.read_c_triage_total = std::max(state.read_c_triage_total,end);

    state.write_c_vic_loc[area] = end;
    state.write_c_triage_total = end;
    state.write_time[agent] = end;
    
    std::erase(state.c_vic_loc[area], vic_awake);
    for (auto a : state.agents) {
      std::erase(state.c_seen[a],vic_awake);
      state.read_c_seen[a] = std::max(state.read_c_seen[a],end);
      state.write_c_seen[a] = end;
    }
    state.c_triage_total = state.c_triage_total + 1; 
    state.time[agent] = end;

    return state;
  }
  else {
    return std::nullopt;
  }
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

  if (state.agent_loc[agent] == c_area && end <= 900 && state.hall_blockage[c_area][n_area] == 0) {

    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);
    state.read_hall_blockage[c_area][n_area] = std::max(state.read_hall_blockage[c_area][n_area],end);
    state.read_c_seen[agent] = std::max(state.read_c_seen[agent],end);
    state.read_r_seen[agent] = std::max(state.read_r_seen[agent],end);
    state.read_visited[agent][n_area] = std::max(state.read_visited[agent][n_area],end);
    state.read_times_searched[agent] = std::max(state.read_times_searched[agent],end);

    state.write_agent_loc[agent] = end;
    state.write_c_seen[agent] = end;
    state.write_r_seen[agent] = end;
    state.write_visited[agent][n_area] = end;
    state.write_time[agent] = end;
    state.write_times_searched[agent] = end;

    state.agent_loc[agent] = n_area;
    state.c_seen[agent].clear();
    state.r_seen[agent].clear();
    
    if (state.visited[agent].find(n_area) == state.visited[agent].end()) {
      state.visited[agent][n_area] = 1;
      state.seed++;
    }
    else {
      state.visited[agent][n_area] = 1 + state.visited[agent][n_area];
      state.seed++;
    }
    state.time[agent] = end;

    state.times_searched[agent] = 0;

    if (!state.loc_tracker[agent].empty()) {
      state.loc_tracker[agent].pop_back();
    }
    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double move(State pre_state, State post_state, Args args) {
  return 1;
}

template <class State> std::optional<State> clear_hall_block(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.hall_blockage[c_area][n_area] > 0 && state.agent_loc[agent] == c_area && 
      state.role[agent] == "engineer" && end <= 900) {
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_hall_blockage[c_area][n_area] = std::max(state.read_hall_blockage[c_area][n_area],end);
    state.read_hall_blockage[n_area][c_area] = std::max(state.read_hall_blockage[n_area][c_area],end);
    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_hall_blockage[c_area][n_area] = end;
    state.write_hall_blockage[n_area][c_area] = end;
    state.write_time[agent] = end;

    state.hall_blockage[c_area][n_area]--;
    state.hall_blockage[n_area][c_area]--;
    state.time[agent] = end;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double clear_hall_block(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> clear_room_block(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  if (state.room_blocks[area] > 0 && state.agent_loc[agent] == area && 
      state.role[agent] == "engineer" && end <= 900) {
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_room_blocks[area] = std::max(state.read_room_blocks[area],end);
    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_room_blocks[area] = end;
    state.write_time[agent] = end;

    if (!state.c_vic_loc[area].empty()) {
      int c_obs = 0;
      std::string c_vic;
      for (auto c: state.c_vic_loc[area]) {
        if (state.obs[c]) {
          c_obs++;
          c_vic = c;
        }
      }
      if (state.room_blocks[area] == c_obs) {
        state.read_obs[c_vic] = std::max(state.read_obs[c_vic],end);
        state.write_obs[c_vic] = end;
        state.obs[c_vic] = false;
      }
    }
    else {
      if (!state.r_vic_loc[area].empty()) {
        int r_obs = 0;
        std::string r_vic;
        for (auto r: state.r_vic_loc[area]) {
          if (state.obs[r]) {
            r_obs++;
            r_vic = r;
          }
        }
        if (state.room_blocks[area] == r_obs) {
          state.read_obs[r_vic] = std::max(state.read_obs[r_vic],end);
          state.write_obs[r_vic] = end;
          state.obs[r_vic] = false;
        }
      }
    }

    state.room_blocks[area]--;
    state.time[agent] = end;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double clear_room_block(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> pickup_vic(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.agent_loc[agent] == area && state.role[agent] == "searcher" &&
      state.holding[agent] == "NONE" && state.r_seen[agent].size() > 0 &&
      end <= 900) {
    
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_holding[agent] = std::max(state.read_holding[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_holding[agent] = end;
    state.write_r_vic_loc[area] = end;
    state.write_time[agent] = end;

    std::string r_vic = state.r_seen[agent].back();
    state.holding[agent] = r_vic;
    std::erase(state.r_vic_loc[area],r_vic);
    for (auto a : state.agents) {
      std::erase(state.r_seen[a],r_vic);
      state.read_r_seen[a] = std::max(state.read_r_seen[a],end);
      state.write_r_seen[a] = end;
    }

    state.time[agent] = end;
    return state;
  }
  else { 
    return std::nullopt;
  }
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

  if (state.agent_loc[agent] == area && state.role[agent] == "searcher" &&
      state.holding[agent] != "NONE" && end <= 900) {
    
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_holding[agent] = std::max(state.read_holding[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_holding[agent] = end;
    state.write_r_vic_loc[area] = end;
    state.write_time[agent] = end;

    std::string r_vic = state.holding[agent];
    state.holding[agent] = "NONE";
    state.r_vic_loc[area].push_back(r_vic);
    state.r_seen[agent].push_back(r_vic);
    state.read_r_seen[agent] = std::max(state.read_r_seen[agent],end);
    state.write_r_seen[agent] = end;

    state.time[agent] = end;
    return state;
  }
  else { 
    return std::nullopt;
  }
}

template <class State> double put_down_vic(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> change_to_medic(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.role[agent] != "medic" && end <= 900 && state.holding[agent] == "NONE") {
   state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
   state.read_role[agent] = std::max(state.read_role[agent],end);
   state.read_time[agent] = std::max(state.read_time[agent],end);
   state.read_holding[agent] = std::max(state.read_holding[agent],end);

   state.write_role[agent] = end;
   state.write_time[agent] = end;
   state.write_holding[agent] = end;
   
   state.role[agent] = "medic";
   state.time[agent] = end;
   return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double change_to_medic(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> change_to_engineer(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.role[agent] != "engineer" && end <= 900 && state.holding[agent] == "NONE") {
   state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
   state.read_role[agent] = std::max(state.read_role[agent],end);
   state.read_time[agent] = std::max(state.read_time[agent],end);
   state.read_holding[agent] = std::max(state.read_holding[agent],end);

   state.write_role[agent] = end;
   state.write_time[agent] = end;
   state.write_holding[agent] = end;
   
   state.role[agent] = "engineer";
   state.time[agent] = end;
   return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double change_to_engineer(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> change_to_searcher(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  if (state.role[agent] != "searcher" && end <= 900 && state.holding[agent] == "NONE") {
   state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
   state.read_role[agent] = std::max(state.read_role[agent],end);
   state.read_time[agent] = std::max(state.read_time[agent],end);
   state.read_holding[agent] = std::max(state.read_holding[agent],end);

   state.write_role[agent] = end;
   state.write_time[agent] = end;
   state.write_holding[agent] = end;
   
   state.role[agent] = "searcher";
   state.time[agent] = end;
   return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double change_to_searcher(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> do_nothing(State state, Args args) {
  auto agent = args["agent"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;
  
  state.read_time[agent] = std::max(state.read_time[agent],end);
  state.write_time[agent] = end;
  state.time[agent] = end;
  return state;
}

template <class State> double do_nothing(State pre_state, State post_state, Args args) {
    return 1;
}

template <class State> std::optional<State> exit(State state, Args args) {
    return state;
}

template <class State> double exit(State pre_state, State post_state, Args args) {
    return 1;
}

// Methods
template <class State> pTasks pick_initial_roles(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  return {1.0,
    {Task("Change_role", Args({{"agent",agent1}})),
     Task("Change_role", Args({{"agent",agent2}})),
     Task("Change_role", Args({{"agent",agent3}})),
     Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}})),
     Task("!exit", Args({{"agent",agent1}})),
     Task("!exit", Args({{"agent",agent2}})),
     Task("!exit", Args({{"agent",agent3}}))}};
}

template <class State> pTasks assign_tasks1a(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900 && 
     (!need_to_triage || state.time[agent1] > 885 || state.time[agent2] > 885 || 
      state.time[agent3] > 885)) {
    return {1.0/6,
          {Task("Do_task", Args({{"agent",agent1}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent3}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks1b(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900 && 
     (!need_to_triage || state.time[agent1] > 885 || state.time[agent2] > 885 || 
      state.time[agent3] > 885)) {
    return {1.0/6,
          {Task("Do_task", Args({{"agent",agent1}})),
           Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks1c(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900 && 
     (!need_to_triage || state.time[agent1] > 885 || state.time[agent2] > 885 || 
      state.time[agent3] > 885)) {
    return {1.0/6,
          {Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Do_task", Args({{"agent",agent3}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks1d(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900 && 
     (!need_to_triage || state.time[agent1] > 885 || state.time[agent2] > 885 || 
      state.time[agent3] > 885)) {
    return {1.0/6,
          {Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks1e(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900 && 
     (!need_to_triage || state.time[agent1] > 885 || state.time[agent2] > 885 || 
      state.time[agent3] > 885)) {
    return {1.0/6,
          {Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks1f(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900 && 
     (!need_to_triage || state.time[agent1] > 885 || state.time[agent2] > 885 || 
      state.time[agent3] > 885)) {
    return {1.0/6,
          {Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks triage_crit_vic(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  bool need_to_triage = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && !state.c_seen[a].empty() &&
        state.agent_loc[a] == state.agent_loc[agent1] &&
        state.agent_loc[a] == state.agent_loc[agent2] &&
        state.agent_loc[a] == state.agent_loc[agent3]) {
      need_to_triage = true;
    }
  }

  if (state.time[agent1] <= 885 && state.time[agent2] <= 885 && state.time[agent3] <= 885 && 
      need_to_triage) {
    return {1.0,
          {Task("Wake_and_triage_crit", Args({{"agent1",agent1},
                                              {"agent2",agent2},
                                              {"agent3",agent3},
                                              {"area",state.agent_loc[agent1]}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks wake_and_triage(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  auto area = args["area"];
  std::string medic;
  std::string non_medic1;
  std::string non_medic2;

  if (state.role[agent1] == "medic") {
    medic = agent1;
    non_medic1 = agent2;
    non_medic2 = agent3;
  }
  else {
    if (state.role[agent2] == "medic") {
      medic = agent2;
      non_medic1 = agent1;
      non_medic2 = agent3;
    }
    else {
      medic = agent3;
      non_medic1 = agent1;
      non_medic2 = agent2;
    }
  }

  std::string duration_wake;
  std::string start_wake_medic;
  std::string start_wake_non1;
  std::string start_wake_non2;

  duration_wake = std::to_string(7);

  int start_num_wake_medic = std::max({state.write_agent_loc[medic],
                               state.write_agent_loc[non_medic1],
                               state.write_agent_loc[non_medic2],
                               state.write_role[medic],
                               state.write_role[non_medic1],
                               state.write_role[non_medic2],
                               state.write_c_seen[medic],
                               state.write_c_seen[non_medic1],
                               state.write_c_seen[non_medic2]});

  int start_num_wake_non1 = std::max({start_num_wake_medic,
                                      state.read_help_wake[non_medic1],
                                      state.read_time[non_medic1]});

  int start_num_wake_non2 = std::max({start_num_wake_medic,
                                      state.read_help_wake[non_medic2],
                                      state.read_time[non_medic2]});

  std::string c = state.c_seen[medic].back();
  start_num_wake_medic = std::max({start_num_wake_medic,
                                      state.read_help_wake[medic],
                                      state.read_help_wake[non_medic1],
                                      state.read_help_wake[non_medic2],
                                      state.read_c_awake[c],
                                      state.read_time[medic]});

  start_wake_medic = std::to_string(start_num_wake_medic);
  start_wake_non1 = std::to_string(start_num_wake_non1);
  start_wake_non2 = std::to_string(start_num_wake_non2);

  std::string duration_triage;
  std::string start_triage;

  duration_triage = std::to_string(8);
  start_triage = std::to_string(start_num_wake_medic + 8);
  return {1,
         {Task("!wakeCrit",Args({{"agent",non_medic1},
                                 {"area",area},
                                 {"start",start_wake_non1},
                                 {"duration",duration_wake}})),
          Task("!wakeCrit",Args({{"agent",non_medic2},
                                 {"area",area},
                                 {"start",start_wake_non2},
                                 {"duration",duration_wake}})),
          Task("!wakeCrit",Args({{"agent",medic},
                                 {"area",area},
                                 {"start",start_wake_medic},
                                 {"duration",duration_wake}})),
          Task("!triageCrit",Args({{"agent",medic},
                                   {"area",area},
                                   {"start",start_triage},
                                   {"duration",duration_triage}}))}};
}

template <class State> pTasks assign_tasks2a(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] >= 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {0.5,
          {Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent3}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks2b(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] >= 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {0.5,
          {Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks3a(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] < 900 && state.time[agent2] >= 900 && state.time[agent3] < 900) {
    return {0.5,
          {Task("Do_task", Args({{"agent",agent1}})),
           Task("Do_task", Args({{"agent",agent3}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks3b(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] < 900 && state.time[agent2] >= 900 && state.time[agent3] < 900) {
    return {0.5,
          {Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks4a(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] >= 900) {
    return {0.5,
          {Task("Do_task", Args({{"agent",agent1}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks4b(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] >= 900) {
    return {0.5,
          {Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks5(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] < 900 && state.time[agent2] >= 900 && state.time[agent3] >= 900) {
    return {1.0,
          {Task("Do_task", Args({{"agent",agent1}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks6(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] >= 900 && state.time[agent2] < 900 && state.time[agent3] >= 900) {
    return {1.0,
          {Task("Do_task", Args({{"agent",agent2}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks7(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] >= 900 && state.time[agent2] >= 900 && state.time[agent3] < 900) {
    return {1.0,
          {Task("Do_task", Args({{"agent",agent3}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks8(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] >= 900 && state.time[agent2] >= 900 && state.time[agent3] < 900) {
    return {1.0,{}};
  }
  return {0,{}};
}

template <class State> pTasks choose_medic(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] != "medic" && state.holding[agent] == "NONE") {
  
    std::string duration;
    std::string start;

    if (state.agent_loc[agent] == "entrance") {
      duration = std::to_string(5);
    }
    else {
      duration = std::to_string(30);
    }

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.write_holding[agent],
                              state.read_role[agent],
                              state.read_time[agent]});

    start = std::to_string(start_num);

    return {1.0/3,
      {Task("!change_to_medic", Args({{"agent", agent},
                                     {"start",start},
                                     {"duration",duration}}))}};
  }
  return {0,{}};

}

template <class State> pTasks choose_engineer(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] != "engineer" && state.holding[agent] == "NONE") {
  
    std::string duration;
    std::string start;

    if (state.agent_loc[agent] == "entrance") {
      duration = std::to_string(5);
    }
    else {
      duration = std::to_string(30);
    }

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.write_holding[agent],
                              state.read_role[agent],
                              state.read_time[agent]});

    start = std::to_string(start_num);

    return {1.0/3,
      {Task("!change_to_engineer", Args({{"agent", agent},
                                     {"start",start},
                                     {"duration",duration}}))}};
  }
  return {0,{}};

}

template <class State> pTasks choose_searcher(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] != "searcher" && state.holding[agent] == "NONE") {
  
    std::string duration;
    std::string start;

    if (state.agent_loc[agent] == "entrance") {
      duration = std::to_string(5);
    }
    else {
      duration = std::to_string(30);
    }

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.write_holding[agent],
                              state.read_role[agent],
                              state.read_time[agent]});

    start = std::to_string(start_num);

    return {1.0/3,
      {Task("!change_to_searcher", Args({{"agent", agent},
                                     {"start",start},
                                     {"duration",duration}}))}};
  }
  return {0,{}};

}

template <class State> pTasks medic_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "medic") {
    return {1.0,
      {Task("Do_medic_task", Args({{"agent", agent}}))}};
  }
  return {0,{}};

}

template <class State> pTasks searcher_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "searcher") {
    return {1.0,
      {Task("Do_searcher_task", Args({{"agent", agent}}))}};
  }
  return {0,{}};

}

template <class State> pTasks engineer_task(State state, Args args) {
  auto agent = args["agent"];

  if (state.role[agent] == "engineer") {
    return {1.0,
      {Task("Do_engineer_task", Args({{"agent", agent}}))}};
  }
  return {0,{}};

}

template <class State> pTasks search_medic(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "medic" && state.agent_loc[agent] != "entrance" &&
      state.r_seen[agent].empty() && state.time[agent] <= 890) {
    double prob;
    prob = (0.95 - 0.10*state.times_searched[agent]);
    if (prob < 0) {
      prob = 0;
    }

    std::string duration;
    std::string start;

    duration = std::to_string(10);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.read_time[agent],
                              state.read_times_searched[agent]});
 

    if (state.c_triage_total != state.c_max) {
      for (auto c : state.c_vic_loc[state.agent_loc[agent]]) {
        if (!in(c,state.c_seen[agent]) && !state.obs[c]) {
          start_num = std::max(start_num,state.read_c_seen[agent]);
         
        }
      }
    }
    else {
      if (state.r_triage_total != state.r_max) { 
        for (auto r : state.r_vic_loc[state.agent_loc[agent]]) {
          if (!in(r,state.r_seen[agent]) && !state.obs[r]) {
            start_num = std::max(start_num,state.read_r_seen[agent]);
            break;
          }
        }
      }
    }

    start = std::to_string(start_num);

    return {prob,
      {Task("!search",Args({{"agent",agent},
                            {"area",state.agent_loc[agent]},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks triage_medic(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "medic" && !state.r_seen[agent].empty() &&
      state.time[agent] <= 893) {

    std::string duration;
    std::string start;

    duration = std::to_string(7);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.write_r_seen[agent],
                              state.read_time[agent],
                              state.read_r_seen[agent],
                              state.read_r_triage_total,
                              state.read_r_vic_loc[state.agent_loc[agent]]});
 

    start = std::to_string(start_num);

    return {1,
      {Task("!triageReg",Args({{"agent",agent},
                            {"area",state.agent_loc[agent]},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks move_medic(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "medic" && state.r_seen[agent].empty() &&
      state.time[agent] <= 890) {
    double prob;
    if (state.agent_loc[agent] == "entrance") {
      prob = 0.95;
    }
    else {
      prob = (0.0 + 0.10*state.times_searched[agent]);
      if (prob > 0.95) {
        prob = 0.95;
      }
    }

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      int stopper = 0;
      while (n_area == state.agent_loc[agent] ||
            state.hall_blockage[state.agent_loc[agent]][n_area] > 0) {
        n_area = sample_loc(state.rooms,state.visited[agent],state.seed);
        state.seed++;
        stopper++;
        if (stopper > (state.rooms.size()*2)) {
          return {0,{}};
        } 
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    std::string duration;
    std::string start;

    duration = std::to_string(10);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_hall_blockage[state.agent_loc[agent]][n_area],
                              state.read_time[agent],
                              state.read_agent_loc[agent],
                              state.read_c_seen[agent],
                              state.read_r_seen[agent],
                              state.read_visited[agent][n_area],
                              state.read_times_searched[agent]});
 

    start = std::to_string(start_num);

    return {prob,
      {Task("!move",Args({{"agent",agent},
                            {"c_area",state.agent_loc[agent]},
                            {"n_area",n_area},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks change_medic(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "medic" && state.r_seen[agent].empty() &&
      state.time[agent] <= 870) {

    return {0.05,
      {Task("Change_role",Args({{"agent",agent}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks clear_room_blocks_engineer(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "engineer" && state.room_blocks[state.agent_loc[agent]] > 0 &&
      state.time[agent] <= 895) {
    double prob = 0.0 + 0.10*state.room_blocks[state.agent_loc[agent]];
    if (prob > 0.95) {
      prob = 0.95;
    }
    return {prob,
      {Task("Break_room_blocks",Args({{"agent",agent},
                            {"area",state.agent_loc[agent]}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks break_a_room_block(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.role[agent] == "engineer" && state.room_blocks[area] > 0 &&
      state.time[agent] <= 895) {
    double prob;
    if (state.room_blocks[area] == 1) {
      prob = 1;
    }
    else {
      prob = 0.5;
    }

    std::string duration;
    std::string start;

    duration = std::to_string(5);

    int start_num = std::max({state.write_room_blocks[area],
                              state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.read_room_blocks[area],
                              state.read_time[agent]});

    
    if (!state.c_vic_loc[area].empty()) {
      int c_obs = 0;
      std::string c_vic;
      for (auto c: state.c_vic_loc[area]) {
        if (state.obs[c]) {
          c_obs++;
          c_vic = c;
        }
      }
      if (state.room_blocks[area] == c_obs) {
        start_num = std::max(start_num,state.read_obs[c_vic]);
      }
    }
    else {
      if (!state.r_vic_loc[area].empty()) {
        int r_obs = 0;
        std::string r_vic;
        for (auto r: state.r_vic_loc[area]) {
          if (state.obs[r]) {
            r_obs++;
            r_vic = r;
          }
        }
        if (state.room_blocks[area] == r_obs) {
          start_num = std::max(start_num,state.read_obs[r_vic]);
        }
      }
    }
    start = std::to_string(start_num);
    return {prob,
      {Task("!clear_room_block",Args({{"agent",agent},
                            {"area",area},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks break_some_room_blocks(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.role[agent] == "engineer" && state.room_blocks[area] > 1 &&
      state.time[agent] <= 895) {

    std::string duration;
    std::string start;

    duration = std::to_string(5);

    int start_num = std::max({state.write_room_blocks[area],
                              state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.read_room_blocks[area],
                              state.read_time[agent]});

    
    if (!state.c_vic_loc[area].empty()) {
      int c_obs = 0;
      std::string c_vic;
      for (auto c: state.c_vic_loc[area]) {
        if (state.obs[c]) {
          c_obs++;
          c_vic = c;
        }
      }
      if (state.room_blocks[area] == c_obs) {
        start_num = std::max(start_num,state.read_obs[c_vic]);
      }
    }
    else {
      if (!state.r_vic_loc[area].empty()) {
        int r_obs = 0;
        std::string r_vic;
        for (auto r: state.r_vic_loc[area]) {
          if (state.obs[r]) {
            r_obs++;
            r_vic = r;
          }
        }
        if (state.room_blocks[area] == r_obs) {
          start_num = std::max(start_num,state.read_obs[r_vic]);
        }
      }
    }
    start = std::to_string(start_num);

    return {0.5,
      {Task("!clear_room_block",Args({{"agent",agent},
                            {"area",area},
                            {"start",start},
                            {"duration",duration}})),
       Task("Break_room_blocks",Args({{"agent",agent},
                                      {"area",area}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks move_engineer(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "engineer" && state.time[agent] <= 885) {
    double prob;
    if (state.agent_loc[agent] == "entrance") {
      prob = 0.95;
    }
    else {
      prob = (0.95 - 0.10*state.room_blocks[state.agent_loc[agent]]);
      if (prob < 0) {
        prob = 0;
      }
    }

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      while (n_area == state.agent_loc[agent]) {
        n_area = sample_loc(state.rooms,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    return {prob,
      {Task("Try_to_move",Args({{"agent",agent},
                            {"c_area",state.agent_loc[agent]},
                            {"n_area",n_area}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks just_move_engineer(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  if (state.role[agent] == "engineer" && state.time[agent] <= 885 &&
      state.hall_blockage[c_area][n_area] == 0) {

    std::string duration;
    std::string start;

    duration = std::to_string(15);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_hall_blockage[c_area][n_area],
                              state.read_time[agent],
                              state.read_agent_loc[agent],
                              state.read_c_seen[agent],
                              state.read_r_seen[agent],
                              state.read_visited[agent][n_area],
                              state.read_times_searched[agent]});
 

    start = std::to_string(start_num);

    return {0.99,
      {Task("!move",Args({{"agent",agent},
                            {"c_area",c_area},
                            {"n_area",n_area},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks clear_hall_engineer(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  if (state.role[agent] == "engineer" && state.time[agent] <= 895 &&
      state.hall_blockage[c_area][n_area] > 0) {

    std::string duration;
    std::string start;

    duration = std::to_string(5);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_hall_blockage[c_area][n_area],
                              state.write_role[agent],
                              state.read_time[agent],
                              state.read_hall_blockage[c_area][n_area]});
 

    start = std::to_string(start_num);

    return {0.99,
      {Task("!clear_hall_block",Args({{"agent",agent},
                            {"c_area",c_area},
                            {"n_area",n_area},
                            {"start",start},
                            {"duration",duration}})),
       Task("Try_to_move",Args({{"agent",agent},
                                {"c_area",c_area},
                                {"n_area",n_area}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks fail_to_move_engineer(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  if (state.role[agent] == "engineer" && state.time[agent] > 895) {
    return {1,{}};
  }  
  return {0.01,{}};
}

template <class State> pTasks change_engineer(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "engineer" && state.time[agent] <= 870) {

    return {0.05,
      {Task("Change_role",Args({{"agent",agent}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks search_searcher(State state, Args args) {
  auto agent = args["agent"];
  bool medic_here = false;
  for (auto a : state.agents) {
    if (state.role[a] == "medic" && 
        state.agent_loc[a] == state.agent_loc[agent]) {
      medic_here = true;
    }
  }
  if (state.role[agent] == "searcher" && state.agent_loc[agent] != "entrance" &&
      (state.r_seen[agent].empty() || medic_here) && state.time[agent] <= 895) {
    double prob;
    prob = (0.95 - 0.10*state.times_searched[agent]);
    if (prob < 0) {
      prob = 0;
    }

    std::string duration;
    std::string start;

    duration = std::to_string(5);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.read_time[agent],
                              state.read_times_searched[agent]});
 

    if (state.c_triage_total != state.c_max) {
      for (auto c : state.c_vic_loc[state.agent_loc[agent]]) {
        if (!in(c,state.c_seen[agent]) && !state.obs[c]) {
          start_num = std::max(start_num,state.read_c_seen[agent]);
         
        }
      }
    }
    else {
      if (state.r_triage_total != state.r_max) { 
        for (auto r : state.r_vic_loc[state.agent_loc[agent]]) {
          if (!in(r,state.r_seen[agent]) && !state.obs[r]) {
            start_num = std::max(start_num,state.read_r_seen[agent]);
            break;
          }
        }
      }
    }

    start = std::to_string(start_num);

    return {prob,
      {Task("!search",Args({{"agent",agent},
                            {"area",state.agent_loc[agent]},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks move_victim_searcher(State state, Args args) {
  auto agent = args["agent"];
  bool medic_here = false;
  std::string n_area = state.agent_loc[agent];
  if (state.loc_tracker[agent].empty()) {
    int stopper = 0;
    while (n_area == state.agent_loc[agent] ||
          state.hall_blockage[state.agent_loc[agent]][n_area] > 0) {
      n_area = sample_loc(state.rooms,state.visited[agent],state.seed);
      state.seed++;
      stopper++;
      if (stopper > (state.rooms.size()*2)) {
        return {0,{}};
      } 
    }
  }
  else {
    n_area = state.loc_tracker[agent].back();
  }

  for (auto a : state.agents) {
    if (state.role[a] == "medic") {
      n_area = state.agent_loc[a];
      if (n_area == state.agent_loc[agent]) {
        medic_here = true;
      }
    }
  }

  if (state.role[agent] == "searcher" && !state.r_seen[agent].empty() &&
      !medic_here && state.time[agent] <= 893) {

    std::string duration_pickup;
    std::string start_pickup;

    duration_pickup = std::to_string(7);

    int start_num_pickup = std::max({state.write_agent_loc[agent],
                              state.write_role[agent],
                              state.write_r_seen[agent],
                              state.write_holding[agent],
                              state.read_time[agent],
                              state.read_holding[agent],
                              state.read_r_seen[agent],
                              state.read_r_vic_loc[state.agent_loc[agent]]});
 

    start_pickup = std::to_string(start_num_pickup);
    
    std::string duration_move;
    std::string start_move;

    duration_move = std::to_string(5);

    int start_num_move = start_num_pickup + 1;

    start_move = std::to_string(start_num_move);

    std::string duration_putdown;
    std::string start_putdown;

    duration_putdown = std::to_string(1);

    int start_num_putdown = start_num_move + 5;

    start_putdown = std::to_string(start_num_putdown);

    return {1,
      {Task("!pickup_vic",Args({{"agent",agent},
                            {"area",state.agent_loc[agent]},
                            {"start",start_pickup},
                            {"duration",duration_pickup}})),
       Task("!move",Args({{"agent",agent},
                          {"c_area",state.agent_loc[agent]},
                          {"n_area",n_area},
                          {"start",start_move},
                          {"duration",duration_move}})),
       Task("!put_down_vic",Args({{"agent",agent},
                                 {"n_area",n_area},
                                 {"start",start_putdown},
                                 {"duration",duration_putdown}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks move_searcher(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "searcher" && state.r_seen[agent].empty() &&
      state.time[agent] <= 895) {
    double prob;
    if (state.agent_loc[agent] == "entrance") {
      prob = 0.95;
    }
    else {
      prob = (0.0 + 0.10*state.times_searched[agent]);
      if (prob > 0.95) {
        prob = 0.95;
      }
    }

    std::string n_area = state.agent_loc[agent];
    if (state.loc_tracker[agent].empty()) {
      int stopper = 0;
      while (n_area == state.agent_loc[agent] ||
            state.hall_blockage[state.agent_loc[agent]][n_area] > 0) {
        n_area = sample_loc(state.rooms,state.visited[agent],state.seed);
        state.seed++;
        stopper++;
        if (stopper > (state.rooms.size()*2)) {
          return {0,{}};
        } 
      }
    }
    else {
      n_area = state.loc_tracker[agent].back();
    }

    std::string duration;
    std::string start;

    duration = std::to_string(5);

    int start_num = std::max({state.write_agent_loc[agent],
                              state.write_hall_blockage[state.agent_loc[agent]][n_area],
                              state.read_time[agent],
                              state.read_agent_loc[agent],
                              state.read_c_seen[agent],
                              state.read_r_seen[agent],
                              state.read_visited[agent][n_area],
                              state.read_times_searched[agent]});
 

    start = std::to_string(start_num);

    return {prob,
      {Task("!move",Args({{"agent",agent},
                            {"c_area",state.agent_loc[agent]},
                            {"n_area",n_area},
                            {"start",start},
                            {"duration",duration}}))}};
  }  
  return {0,{}};
}

template <class State> pTasks change_searcher(State state, Args args) {
  auto agent = args["agent"];
  if (state.role[agent] == "searcher" && state.r_seen[agent].empty() &&
      state.time[agent] <= 870) {

    return {0.05,
      {Task("Change_role",Args({{"agent",agent}}))}};
  }  
  return {0,{}};
}

class TeamSARState {
  public:
    std::vector<std::string> agents;

    std::vector<std::string> rooms;

    std::unordered_map<std::string, std::string> role;
    std::unordered_map<std::string, int> read_role;
    std::unordered_map<std::string, int> write_role;

    std::unordered_map<std::string, std::string> agent_loc;
    std::unordered_map<std::string, int> read_agent_loc;
    std::unordered_map<std::string, int> write_agent_loc;

    std::unordered_map<std::string, std::vector<std::string>> c_vic_loc;
    std::unordered_map<std::string, int> read_c_vic_loc;
    std::unordered_map<std::string, int> write_c_vic_loc;

    std::unordered_map<std::string, std::vector<std::string>> r_vic_loc;
    std::unordered_map<std::string, int> read_r_vic_loc;
    std::unordered_map<std::string, int> write_r_vic_loc;

    std::unordered_map<std::string, bool> obs;
    std::unordered_map<std::string, int> read_obs;
    std::unordered_map<std::string, int> write_obs;

    std::unordered_map<std::string, bool> c_awake;
    std::unordered_map<std::string, int> read_c_awake;
    std::unordered_map<std::string, int> write_c_awake;

    std::unordered_map<std::string, std::unordered_map<std::string,int>> hall_blockage;
    std::unordered_map<std::string, std::unordered_map<std::string,int>> read_hall_blockage;
    std::unordered_map<std::string, std::unordered_map<std::string,int>> write_hall_blockage;

    std::unordered_map<std::string, int> room_blocks;
    std::unordered_map<std::string, int> read_room_blocks;
    std::unordered_map<std::string, int> write_room_blocks;

    std::unordered_map<std::string, bool> help_wake;
    std::unordered_map<std::string, int> read_help_wake;
    std::unordered_map<std::string, int> write_help_wake;

    std::unordered_map<std::string,std::string> holding; 
    std::unordered_map<std::string,int> read_holding;
    std::unordered_map<std::string,int> write_holding;

    int c_triage_total;
    int read_c_triage_total;
    int write_c_triage_total;

    int r_triage_total;
    int read_r_triage_total;
    int write_r_triage_total;

    int c_max;
    int r_max;

    std::unordered_map<std::string, std::vector<std::string>> c_seen;
    std::unordered_map<std::string, int> read_c_seen;
    std::unordered_map<std::string, int> write_c_seen;

    std::unordered_map<std::string, std::vector<std::string>> r_seen;
    std::unordered_map<std::string, int> read_r_seen;
    std::unordered_map<std::string, int> write_r_seen;

    std::unordered_map<std::string, int> time;
    std::unordered_map<std::string, int> read_time;
    std::unordered_map<std::string, int> write_time;

    std::unordered_map<std::string, int> times_searched;
    std::unordered_map<std::string, int> read_times_searched;
    std::unordered_map<std::string, int> write_times_searched;

    std::unordered_map<std::string, std::unordered_map<std::string, int>> visited; 
    std::unordered_map<std::string, std::unordered_map<std::string, int>> read_visited;
    std::unordered_map<std::string, std::unordered_map<std::string, int>> write_visited;
    
    // Not part of the state representation!
    std::unordered_map<std::string, std::vector<std::string>> loc_tracker;
    int seed = 100;

    nlohmann::json to_json() {
      return nlohmann::json{{"agents", this->agents},
               {"rooms",this->rooms},
               {"role",this->role},
               {"agent_loc",this->agent_loc},
               {"c_vic_loc",this->c_vic_loc},
               {"r_vic_loc",this->r_vic_loc},
               {"obs",this->obs},
               {"c_awake",this->c_awake},
               {"hall_blockage",this->hall_blockage},
               {"room_blocks",this->room_blocks},
               {"help_wake",this->help_wake},
               {"holding",this->holding},
               {"c_triage_total",this->c_triage_total},
               {"r_triage_total",this->r_triage_total},
               {"c_max", this->c_max},
               {"r_max",this->r_max},
               {"c_seen",this->c_seen},
               {"r_max",this->r_seen},
               {"time",this->time},
               {"times_searched",this->times_searched},
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
      Operators<TeamSARState>({{"!search",search},
                           {"!triageReg",triageReg},
                           {"!wakeCrit",wakeCrit},
                           {"!triageCrit",triageCrit},
                           {"!clear_hall_block",clear_hall_block},
                           {"!clear_room_block",clear_room_block},
                           {"!pickup_vic",pickup_vic},
                           {"!put_down_vic",put_down_vic},
                           {"!change_to_medic",change_to_medic},
                           {"!change_to_engineer",change_to_engineer},
                           {"!change_to_searcher",change_to_searcher},
                           {"!move",move},
                           {"!do_nothing",do_nothing},
                           {"!exit",exit}});

    pOperators<TeamSARState> poperators = 
      pOperators<TeamSARState>({{"!search",search},
                           {"!triageReg",triageReg},
                           {"!wakeCrit",wakeCrit},
                           {"!triageCrit",triageCrit},
                           {"!clear_hall_block",clear_hall_block},
                           {"!clear_room_block",clear_room_block},
                           {"!pickup_vic",pickup_vic},
                           {"!put_down_vic",put_down_vic},
                           {"!change_to_medic",change_to_medic},
                           {"!change_to_engineer",change_to_engineer},
                           {"!change_to_searcher",change_to_searcher},
                           {"!move",move},
                           {"!do_nothing",do_nothing},
                           {"!exit",exit}});


    Methods<TeamSARState> methods =
      Methods<TeamSARState>({{"SAR",
                          {pick_initial_roles}},
                         {"Change_role",
                          {choose_medic,
                           choose_engineer,
                           choose_searcher}},
                         {"Explore",
                          {assign_tasks1a,
                           assign_tasks1b,
                           assign_tasks1c,
                           assign_tasks1d,
                           assign_tasks1e,
                           assign_tasks1f,
                           triage_crit_vic,
                           assign_tasks2a,
                           assign_tasks2b,
                           assign_tasks3a,
                           assign_tasks3b,
                           assign_tasks4a,
                           assign_tasks4b,
                           assign_tasks5,
                           assign_tasks6,
                           assign_tasks7,
                           assign_tasks8}},
                         {"Do_task",
                          {medic_task,
                           searcher_task,
                           engineer_task}},
                         {"Do_medic_task",
                          {search_medic,
                           triage_medic,
                           move_medic,
                           change_medic}},
                         {"Do_engineer_task",
                          {clear_room_blocks_engineer,
                           move_engineer,
                           change_engineer}},
                         {"Do_searcher_task",
                          {search_searcher,
                           move_victim_searcher,
                           move_searcher,
                           change_searcher}},
                         {"Wake_and_triage_crit",
                          {wake_and_triage}},
                         {"Break_room_blocks",
                          {break_a_room_block,
                           break_some_room_blocks}},
                         {"Try_to_move",
                          {just_move_engineer,
                           clear_hall_engineer,
                           fail_to_move_engineer}}});

    TeamSARDomain() {
      std::cout << "Operators: ";
      print(this->operators);

      std::cout << "Method: ";
      print(this->methods);
    };
};
