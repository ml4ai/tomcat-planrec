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
    state.read_r_triage_total = std::max(state.read_r_triage_total,end)
    
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
      if (state.role[a] == "medic") {
        have_medic = true;
      }
      state.read_help_wake[a] = std::max(state.read_help_wake[a],end);
      if (state.help_wake[a]) {
        help_count++;
      }
    }
  }

  if (state.agent_loc[agent] == area && !state.c_seen[agent].empty() && 
      a_count >= 3 && have_medic && end <= 900) {
    
    state.read_c_seen[agent] = std::max(state.read_c_seen[agent],end);
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
    state.read_visited[agent] = std::max(state.read_visited,end);
    state.read_times_searched[agent] = std::max(state.read_times_searched[agent],end);

    state.write_agent_loc[agent] = end;
    state.write_c_seen[agent] = end;
    state.write_r_seen[agent] = end;
    state.write_visited[agent] = end;
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

  if (state.hall_blockage[c_area][n_area] > 0 && state.agent_loc[agent] = c_area && 
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
  auto c_area = args["c_area"];
  auto start = std::stoi(args["start"],nullptr);
  auto duration = std::stoi(args["duration"],nullptr);
  int end = start + duration;

  if (state.room_blocks[c_area] > 0 && state.agent_loc[agent] = c_area && 
      state.role[agent] == "engineer" && end <= 900) {
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_room_blocks[c_area] = std::max(state.read_room_blocks[c_area],end);
    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_room_blocks[c_area] = end;
    state.write_time[agent] = end;

    if (state.c_vic_loc[c_area] != 0) {
      int c_obs = 0;
      std::string c_vic;
      for (auto c: state.c_vic_loc[c_area]) {
        if (state.obs[c]) {
          c_obs++;
          c_vic = c;
        }
      }
      if (room_blocks[c_area] == c_obs) {
        state.read_obs[c_vic] = std::max(state.read_obs[c_vic],end);
        state.write_obs[c_vic] = end;
        state.obs[c_vic] = false;
      }
    }
    else {
      if (state.r_vic_loc[c_area] != 0) {
        int r_obs = 0;
        std::string r_vic;
        for (auto r: state.r_vic_loc[c_area]) {
          if (state.obs[r]) {
            r_obs++;
            r_vic = r;
          }
        }
        if (room_blocks[c_area] == r_obs) {
          state.read_obs[r_vic] = std::max(state.read_obs[r_vic],end);
          state.write_obs[r_vic] = end;
          state.obs[r_vic] = false;
        }
      }
    }

    state.room_blocks[c_area]--;
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
    state.read_r_seen[agent] = std::max(state.read_r_seen[a],end);
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
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
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
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
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
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
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
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
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
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
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
  if (state.time[agent1] < 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
          {Task("Do_task", Args({{"agent",agent3}})),
           Task("Do_task", Args({{"agent",agent2}})),
           Task("Do_task", Args({{"agent",agent1}})),
           Task("Explore", Args({{"agent1",agent1},{"agent2",agent2},{"agent3",agent3}}))}};
  }
  return {0,{}};
}

template <class State> pTasks assign_tasks2a(State state, Args args) {
  auto agent1 = args["agent1"];
  auto agent2 = args["agent2"];
  auto agent3 = args["agent3"];
  if (state.time[agent1] >= 900 && state.time[agent2] < 900 && state.time[agent3] < 900) {
    return {1.0,
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
    return {1.0,
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
    return {1.0,
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
    return {1.0,
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
    return {1.0,
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
    return {1.0,
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

    int start_num;

    if (state.c_triage_total != state.c_max) {
      for (auto c : state.c_vic_loc[state.agent_loc[agent]]) {
        if (!in(c,state.c_seen[agent]) && !state.obs[c]) {
          start_num = std::max({state.write_agent_loc[agent],
                              state.read_c_seen[agent],
                              state.read_time[agent],
                              state.read_times_searched[agent]});
         
        }
      }
    }
    else {
      if (state.r_triage_total != state.r_max) { 
        for (auto r : state.r_vic_loc[area]) {
          if (!in(r,state.r_seen[agent]) && !state.obs[r]) {
            start_num = std::max({state.write_agent_loc[agent],
                              state.read_r_seen[agent],
                              state.read_time[agent],
                              state.read_times_searched[agent]});
            break;
          }
        }
      }
      else {
        start_num = std::max({state.write_agent_loc[agent],
                              state.read_time[agent],
                              state.read_times_searched[agent]});
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
                              state.write.r_seen[agent],
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

    std::string n_area = state.loc[agent];
    if (state.loc_tracker[agent].empty()) {
      int stopper;
      while (n_area == state.loc[agent] &&
            state.hall_blockage[state.agent_loc[agent][n_area]] > 0) {
        n_area = sample_loc(state.rooms,state.visited[agent],state.seed);
        state.seed++;
        stopper++;
        if (stopper > (state.rooms.size()*2)) {
          prob = 0;
          break;
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
                              state.read_visited[agent],
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
  if (state.role[agent] == "engineer" && room_blocks[state.agent_loc[agent]] > 0 &&
      state.time[agent] <= 895) {
    double prob = 0.0 + 0.10*room_blocks[state.agent_loc[agent]];
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
  if (state.role[agent] == "engineer" && room_blocks[state.agent_loc[agent]] > 0 &&
      state.time[agent] <= 895) {
    double prob;
    if (room_blocks[state.agent_loc[agent]] == 1) {
      prob = 1;
    }
    else {
      prob = 0.5;
    }
    return {prob,
      {Task("!clear_room_block",Args({{"agent",agent},
                            {"area",state.agent_loc[agent]}}))}};
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

    std::string n_area = state.loc[agent];
    if (state.loc_tracker[agent].empty()) {
      int stopper;
      while (n_area == state.loc[agent] &&
            state.hall_blockage[state.agent_loc[agent][n_area]] > 0) {
        n_area = sample_loc(state.rooms,state.visited[agent],state.seed);
        state.seed++;
        stopper++;
        if (stopper > (state.rooms.size()*2)) {
          prob = 0;
          break;
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
                              state.read_visited[agent],
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

class SARState {
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
      return nlohmann::json{{"loc", this->loc},
               {"y_vic",this->y_vic},
               {"g_vic",this->g_vic},
               {"y_total",this->y_total},
               {"g_total",this->g_total},
               {"y_seen",this->y_seen},
               {"g_seen",this->g_seen},
               {"left_region",this->left_region},
               {"right_region",this->right_region},
               {"mid_region",this->mid_region},
               {"left_explored",this->left_explored},
               {"right_explored",this->right_explored},
               {"mid_explored",this->mid_explored},
               {"time",this->time},
               {"times_searched", this->times_searched},
               {"visited",this->visited},
               {"y_max",this->y_max},
               {"g_max",this->g_max}};
    }
};

class SARSelector {
  public:
    double mean = 0;
    int sims = 0;

    double selectFunc(int pSims, double c, int r_l, int r_t) {
      return this->mean + ((c*r_l)/r_t)*sqrt(log(pSims)/this->sims);
    }

    double rewardFunc(SARState s) {
      return (50.00*s.y_total + 10.00*s.g_total)/(50.00*s.y_max + 10.00*s.g_max);
    }

};

class SARDomain {
  public:
    Operators<SARState> operators = 
      Operators<SARState>({{"!search",search},
                           {"!triageGreen",triageGreen},
                           {"!triageYellow",triageYellow},
                           {"!move",move},
                           {"!exit",exit}});

    pOperators<SARState> poperators = 
      pOperators<SARState>({{"!search",search},
                           {"!triageGreen",triageGreen},
                           {"!triageYellow",triageYellow},
                           {"!move",move},
                           {"!exit",exit}});


    Methods<SARState> methods =
      Methods<SARState>({{"SAR",
                          {SAR}},
                         {"SAR_O",
                          {sweep_left_O,
                           sweep_right_O,
                           zigzag_left_O,
                           zigzag_right_O}},
                         {"sweep_left_O",
                          {explore_right_to_left_O}},
                         {"sweep_right_O",
                          {explore_left_to_right_O}},
                         {"zigzag_left_O",
                          {explore_mid_left_right_O}},
                         {"zigzag_right_O",
                          {explore_mid_right_left_O}},
                         {"explore_left_region_O",
                          {search_left_O,
                           triageYellow_left_O,
                           triageGreen_left_O,
                           move_left_O,
                           leave_left_O}},
                         {"explore_right_region_O",
                          {search_right_O,
                           triageYellow_right_O,
                           triageGreen_right_O,
                           move_right_O,
                           leave_right_O}},
                         {"explore_mid_region_O",
                          {search_mid_O,
                           triageYellow_mid_O,
                           triageGreen_mid_O,
                           move_mid_O,
                           leave_mid_O}},
                         {"SAR_YF",
                          {sweep_left_YF,
                           sweep_right_YF,
                           zigzag_left_YF,
                           zigzag_right_YF}},
                         {"sweep_left_YF",
                          {explore_right_to_left_YF}},
                         {"sweep_right_YF",
                          {explore_left_to_right_YF}},
                         {"zigzag_left_YF",
                          {explore_mid_left_right_YF}},
                         {"zigzag_right_YF",
                          {explore_mid_right_left_YF}},
                         {"explore_left_region_YF",
                          {search_left_YF,
                           triageYellow_left_YF,
                           triageGreen_left_YF,
                           move_left_YF,
                           leave_left_YF}},
                         {"explore_right_region_YF",
                          {search_right_YF,
                           triageYellow_right_YF,
                           triageGreen_right_YF,
                           move_right_YF,
                           leave_right_YF}},
                         {"explore_mid_region_YF",
                          {search_mid_YF,
                           triageYellow_mid_YF,
                           triageGreen_mid_YF,
                           move_mid_YF,
                           leave_mid_YF}}});

    SARDomain() {
      std::cout << "Operators: ";
      print(this->operators);

      std::cout << "Method: ";
      print(this->methods);
    };
};
