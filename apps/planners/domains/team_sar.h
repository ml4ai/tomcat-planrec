#include "cpphop.h"
#include <math.h>
#include <nlohmann/json.hpp>
#include <string>
#include <algorithm>

using json = nlohmann::ordered_json;

// aux functions
std::string 
sample_loc(std::vector<std::string> region,
           std::unordered_map<std::string, int> visited,
           int seed) {
  std::vector<double> w;
  for (auto a : region) {
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
  return region[s];
}

std::unordered_map<std::string,std::vector<std::string>>
get_loc_seq(json j,
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
sample_loc(std::vector<std::string> region,
           std::unordered_map<std::string, int> visited) {
  std::vector<double> w;
  for (auto a : region) {
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
  return region[s];
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
    state.read_c_triage_total = std::max(state.read_c_triage_total,end);

    if (state.c_triage_total != state.c_max) {
      state.read_c_vic_loc[area] = std::max(state.read_c_vic_loc[area],end);
      for (auto c : state.c_vic_loc[area]) {
        state.read_c_seen[agent] = std::max(state.read_c_seen[agent],end);
        state.read_obs[c] = std::max(state.read_obs[c],end);
        if (!in(c,state.c_seen[agent]) && !state.obs[c]) {
          state.c_seen[agent].push_back(c);
          state.time[agent] = end;

          state.times_searched[agent]++;

          state.write_c_seen[agent] = end;
          return state;
        }
      }
    }


    state.read_r_triage_total = std::max(state.read_r_triage_total,end);
    if (state.r_triage_total != state.r_max) { 
      state.read_r_vic_loc[area] = std::max(state.read_r_vic_loc[area],end);
      for (auto r : state.r_vic_loc[area]) {
        state.read_r_seen[agent] = std::max(state.read_r_seen[agent],end);
        state.read_obs[r] = std::max(state.read_obs[r],end);
        if (!in(r,state.r_seen[agent]) && !state.obs[r]) {
          state.r_seen[agent].push_back(r);
          state.write_r_seen[agent] = end;
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

  if (state.agent_loc[agent] == c_area && end <= 900 && hall_blockage[c_area][n_area] == 0) {

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

  if (state.room_blockage[c_area] > 0 && state.agent_loc[agent] = c_area && 
      state.role[agent] == "engineer" && end <= 900) {
    state.read_agent_loc[agent] = std::max(state.read_agent_loc[agent],end);
    state.read_room_blockage[c_area] = std::max(state.read_room_blockage[c_area],end);
    state.read_role[agent] = std::max(state.read_role[agent],end);
    state.read_time[agent] = std::max(state.read_time[agent],end);

    state.write_room_blockage[c_area] = end;
    state.write_time[agent] = end;

    state.read_c_vic_loc[c_area] = std::max(state.read_c_vic_loc[c_area],end);

    if (state.c_vic_loc[c_area] != 0) {
      int c_obs = 0;
      std::string c_vic;
      for (auto c: state.c_vic_loc[c_area]) {
        state.read_obs[c] = std::max(state.read_obs[c],end);
        if (state.obs[c]) {
          c_obs++;
          c_vic = c;
        }
      }
      if (room_blockage[c_area] == c_obs) {
        state.write_obs[c_vic] = end;
        state.obs[c_vic] = false;
      }
    }
    else {
      state.read_r_vic_loc[c_area] = std::max(state.read_r_vic_loc[c_area],end);
      if (state.r_vic_loc[c_area] != 0) {
        int r_obs = 0;
        std::string r_vic;
        for (auto r: state.r_vic_loc[c_area]) {
          state.read_obs[r] = std::max(state.read_obs[r],end);
          if (state.obs[r]) {
            r_obs++;
            r_vic = r;
          }
        }
        if (room_blockage[c_area] == r_obs) {
          state.write_obs[r_vic] = end;
          state.obs[r_vic] = false;
        }
      }
    }

    state.room_blockage[c_area]--;
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
   state.read_role[agent] = std::max(state.read_role[agent],end);
   state.read_time[agent] = std::max(state.read_time[agent],end);
   state.read_holding[agent] = std::max(state.read_holding[agent],end);

   state.write_role[agent] = end;
   state.write_time[agent] = end;
   state.write_holding[agent] = end;
   
   state.role[agent] = "medic";
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
   state.read_role[agent] = std::max(state.read_role[agent],end);
   state.read_time[agent] = std::max(state.read_time[agent],end);
   state.read_holding[agent] = std::max(state.read_holding[agent],end);

   state.write_role[agent] = end;
   state.write_time[agent] = end;
   state.write_holding[agent] = end;
   
   state.role[agent] = "engineer";
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
   state.read_role[agent] = std::max(state.read_role[agent],end);
   state.read_time[agent] = std::max(state.read_time[agent],end);
   state.read_holding[agent] = std::max(state.read_holding[agent],end);

   state.write_role[agent] = end;
   state.write_time[agent] = end;
   state.write_holding[agent] = end;
   
   state.role[agent] = "searcher";
   return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double change_to_searcher(State pre_state, State post_state, Args args) {
    return 1;
}
template <class State> std::optional<State> exit(State state, Args args) {
    return state;
}

template <class State> double exit(State pre_state, State post_state, Args args) {
    return 1;
}

// Methods

template <class State> pTasks SAR_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.5,
    {Task("SAR_O", Args({{"agent",agent}}))}};
}

template <class State> pTasks sweep_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_left_O",Args({{"agent",agent}}))}};
}

template <class State> pTasks sweep_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_right_O",Args({{"agent",agent}}))}};
}

template <class State> pTasks zigzag_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_left_O",Args({{"agent",agent}}))}};
}

template <class State> pTasks zigzag_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_right_O",Args({{"agent",agent}}))}};
}

template <class State> pTasks explore_left_to_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks explore_right_to_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_left_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_right_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks search_left_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0;
    }
    else {
      prob = (1 - 0.10*state.times_searched);
      if (prob < 0) {
        prob = 0;
      }
    }
    return {prob, 
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_O",Args({{"agent",agent}}))}};
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageGreen_left_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 590 && state.g_seen[agent] && !need_to_move) {
    double prob; 
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    return {prob, 
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageYellow_left_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 405 && state.y_seen[agent] && !need_to_move) {
    double prob;
    if (state.g_seen[agent]) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    return {prob, 
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_left_O(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590) {
    std::string n_area = state.loc[agent];
    if (state.loc_tracker["left"].empty()) {
      while (n_area == state.loc[agent]) {
        n_area = sample_loc(state.left_region,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker["left"].back();
    }

    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.left_region));
    if (need_to_move) {
      return {1, 
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
    }
 
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
        prob = 0;
    }
    else {
        prob = (0.0 + 0.10*state.times_searched);
        if (prob > 1) {
          prob = 1.0;
        }
    }
    if (state.left_explored) {
      prob /= 2;
    }
    return {prob, 
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_left_O(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590) {
    return {1,{}};
  }

  if (state.left_explored) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0;
    }
    else {
      prob = (0.0 + 0.10*state.times_searched)/2;
      if (prob > 0.5) {
        prob = 0.5;
      }
    }
    return {prob,{}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks search_right_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.right_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0;
    }
    else {
      prob = (1.0 - 0.10*state.times_searched);
    }
    return {prob, 
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_O",Args({{"agent",agent}}))}};
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageGreen_right_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.right_region));
  if (state.time <= 590 && state.g_seen[agent] && !need_to_move) {
    double prob; 
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    return {prob, 
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageYellow_right_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.right_region));
  if (state.time <= 405 && state.y_seen[agent] && !need_to_move) {
    double prob;
    if (state.g_seen[agent]) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    return {prob, 
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_right_O(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590) {
    std::string n_area = state.loc[agent];
    if (state.loc_tracker["right"].empty()) {
      while (n_area == state.loc[agent]) {
        n_area = sample_loc(state.right_region,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker["right"].back();
    }
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.right_region));
    if (need_to_move) {
      return {1, 
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
    }

    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
        prob = 0;
    }
    else {
        prob = (0.0 + 0.10*state.times_searched);
        if (prob > 1) {
          prob = 1.0;
        }
    }
    if (state.left_explored) {
      prob /= 2;
    }

    return {prob, 
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_right_O(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590) {
    return {1,{}};
  }

  if (state.right_explored) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0;
    }
    else {
      prob = (0.0 + 0.10*state.times_searched)/2;
      if (prob > 0.5) {
        prob = 0.5;
      }
    }
    return {prob,{}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks search_mid_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.mid_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0;
    }
    else {
      prob = (1.0 - 0.10*state.times_searched);
      if (prob < 0) {
        prob = 0;
      }
    }
    return {prob, 
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_O",Args({{"agent",agent}}))}};
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageGreen_mid_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.mid_region));
  if (state.time <= 590 && state.g_seen[agent] && !need_to_move) {
    double prob; 
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    return {prob, 
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageYellow_mid_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.mid_region));
  if (state.time <= 405 && state.y_seen[agent] && !need_to_move) {
    double prob;
    if (state.g_seen[agent]) {
      prob = 0.5;
    }
    else {
      prob = 1;
    }
    return {prob, 
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_mid_O(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590) {
    std::string n_area = state.loc[agent];
    if (state.loc_tracker["mid"].empty()) {
      while (n_area == state.loc[agent]) {
        n_area = sample_loc(state.mid_region,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker["mid"].back();
    }

    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.mid_region));
    if (need_to_move) {
      return {1, 
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
    }

    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
        prob = 0;
    }
    else {
        prob = (0.0 + 0.10*state.times_searched);
        if (prob > 1) {
          prob = 1.0;
        }
    }
    if (state.mid_explored) {
      prob /= 2;
    }

    return {prob, 
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_mid_O(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590) {
    return {1,{}};
  }

  if (state.mid_explored) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0;
    }
    else {
      prob = (0.0 + 0.10*state.times_searched)/2;
      if (prob > 0.5) {
        prob = 0.5;
      }
    }
    return {prob,{}}; 
  }
  else {
    return {0,{}};
  }
}


template <class State> pTasks SAR_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.5,
    {Task("SAR_YF", Args({{"agent",agent}}))}};
}

template <class State> pTasks sweep_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_left_YF",Args({{"agent",agent}}))}};
}

template <class State> pTasks sweep_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_right_YF",Args({{"agent",agent}}))}};
}

template <class State> pTasks zigzag_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_left_YF",Args({{"agent",agent}}))}};
}

template <class State> pTasks zigzag_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_right_YF",Args({{"agent",agent}}))}};
}

template <class State> pTasks explore_left_to_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks explore_right_to_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_left_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_right_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("!exit",Args({}))}}; 
}

template <class State> pTasks search_left_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
        prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
          prob = (1.0 - 0.10*state.times_searched);
          if (prob < 0) {
            prob = 0;
          }
      }
    }
    return {prob, 
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_YF",Args({{"agent",agent}}))}};
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageGreen_left_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 590 && state.g_seen[agent] && !need_to_move) {
    double prob; 
    if (state.time > 405) {
      prob = 1;
    }
    else {
      prob = 0;
    }
    return {prob, 
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageYellow_left_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 405 && state.y_seen[agent] && !need_to_move) {
    return {1, 
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_left_YF(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590) {
    std::string n_area = state.loc[agent];
    if (state.loc_tracker["left"].empty()) {
      while (n_area == state.loc[agent]) {
        n_area = sample_loc(state.left_region,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker["left"].back();
    }

    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.left_region));
    if (need_to_move) {
      return {1, 
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
    }

    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (0.0 + 0.10*state.times_searched);
        if (prob > 1) {
          prob = 1.0;
        }
      }
    }

    if (state.left_explored) {
      prob /= 2;
    }

    return {prob, 
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_left_YF(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590) {
    return {1,{}};
  }

  if (state.left_explored) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
        prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (0.0 + 0.10*state.times_searched)/2;
        if (prob > 0.5) {
          prob = 0.5;
        }
      }
    }
    return {prob,{}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks search_right_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.right_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (1.0 - 0.10*state.times_searched);
        if (prob < 0) {
          prob = 0;
        }
      }
    }
    return {prob, 
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_YF",Args({{"agent",agent}}))}};
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageGreen_right_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.right_region));
  if (state.time <= 590 && state.g_seen[agent] && !need_to_move) {
    double prob; 
    if (state.time > 405) {
      prob = 1;
    }
    else {
      prob = 0;
    }
    return {prob, 
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageYellow_right_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.right_region));
  if (state.time <= 405 && state.y_seen[agent] && !need_to_move) {
    return {1, 
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_right_YF(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590) {
    std::string n_area = state.loc[agent];
    if (state.loc_tracker["right"].empty()) {
      while (n_area == state.loc[agent]) {
        n_area = sample_loc(state.right_region,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker["right"].back();
    }

    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.right_region));
    if (need_to_move) {
      return {1, 
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
    }

    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (0.0 + 0.10*state.times_searched);
        if (prob > 1) {
          prob = 1.0;
        }
      }
    }

    if (state.right_explored) {
      prob /= 2;
    }

    return {prob, 
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_right_YF(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590) {
    return {1,{}};
  }

  if (state.right_explored) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (0.0 + 0.10*state.times_searched)/2;
        if (prob > 0.5) {
          prob = 0.5;
        }
      }
    }
    return {prob,{}}; 
  }
  else {
    return {0,{}};
  }
}


template <class State> pTasks search_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.mid_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (1.0 - 0.10*state.times_searched);
        if (prob < 0) {
          prob = 0;
        }
      }
    }
    return {prob, 
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_YF",Args({{"agent",agent}}))}};
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageGreen_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.mid_region));
  if (state.time <= 590 && state.g_seen[agent] && !need_to_move) {
    double prob; 
    if (state.time > 405) {
      prob = 1;
    }
    else {
      prob = 0;
    }
    return {prob, 
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks triageYellow_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.mid_region));
  if (state.time <= 405 && state.y_seen[agent] && !need_to_move) {
    return {1, 
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590) {
    std::string n_area = state.loc[agent];
    if (state.loc_tracker["mid"].empty()) {
      while (n_area == state.loc[agent]) {
        n_area = sample_loc(state.mid_region,state.visited[agent],state.seed);
        state.seed++;
      }
    }
    else {
      n_area = state.loc_tracker["mid"].back();
    }

    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.mid_region));
    if (need_to_move) {
      return {1, 
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
    }

    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (0.0 + 0.10*state.times_searched);
        if (prob > 1) {
          prob = 1.0;
        }
      }
    }

    if (state.mid_explored) {
      prob /= 2;
    }

    return {prob, 
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590) {
    return {1,{}};
  }

  if (state.mid_explored) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      prob = 0;
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0;
      }
      else {
        prob = (0.0 + 0.10*state.times_searched)/2;
        if (prob > 0.5) {
          prob = 0.5;
        }
      }
    }
    return {prob,{}}; 
  }
  else {
    return {0,{}};
  }
}

class SARState {
  public:
    std::vector<std::string> agents;

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

    json to_json() {
      return json{{"loc", this->loc},
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
                          {SAR_O,SAR_YF}},
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
