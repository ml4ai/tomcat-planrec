#pragma once

#include "cpphop.h"
#include <math.h>
#include <nlohmann/json.hpp>
#include <string>

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
  if (state.loc[agent] == area && state.time <= 590) {
    if (state.time < 420 && (state.y_vic[area] - state.y_seen[agent])) {
      state.y_seen[agent] = state.y_seen[agent] + 1;
    }

    if ((state.g_vic[area] - state.g_seen[agent])) {
      state.g_seen[agent] = state.g_seen[agent] + 1;
    } 
 
    state.time = state.time + 10;

    state.times_searched++;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double search(State pre_state, State post_state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (pre_state.loc[agent] == area && post_state.loc[agent] == area && pre_state.time <= 590) {
    if (pre_state.time < 420 && (pre_state.y_vic[area] - pre_state.y_seen[agent])) {
      if ((post_state.y_seen[agent] - pre_state.y_seen[agent]) != 1) {
        return 0;
      } 
    }

    if ((pre_state.g_vic[area] - pre_state.g_seen[agent])) {
      if ((post_state.g_seen[agent] - pre_state.g_seen[agent]) != 1) {
        return 0;
      }
    } 
 
    if ((post_state.time - pre_state.time) != 10) {
      return 0;
    } 

    if ((post_state.times_searched - pre_state.times_searched) != 1) {
      return 0;
    }
    return 1;

  }
  else {
    return 0;
  }
}

template <class State> std::optional<State> triageGreen(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.loc[agent] == area && state.g_vic[area] && state.time <= 593) {
    state.g_seen[agent] = state.g_seen[agent] - 1;
    state.g_vic[area] = state.g_vic[area] - 1;
    state.g_total = state.g_total + 1; 
    state.time = state.time + 7;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double triageGreen(State pre_state,State post_state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (pre_state.loc[agent] == area && post_state.loc[agent] == area && pre_state.g_vic[area] && pre_state.time <= 593) {
    if ((pre_state.g_seen[agent] - post_state.g_seen[agent]) == 1 && 
        (pre_state.g_vic[area] - post_state.g_vic[area]) == 1 &&
        (post_state.g_total - pre_state.g_total) == 1 &&
        (post_state.time - pre_state.time) == 7) {
      return 1;
    } 
    return 0;
  }
  else {
    return 0;
  }
}

template <class State> std::optional<State> triageYellow(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.loc[agent] == area && state.y_vic[area] && state.time <= 405) {
    state.y_seen[agent] = state.y_seen[agent] - 1;
    state.y_vic[area] = state.y_vic[area] - 1;
    state.y_total = state.y_total + 1; 
    state.time = state.time + 15;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double triageYellow(State pre_state,State post_state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (pre_state.loc[agent] == area && post_state.loc[agent] == area && pre_state.y_vic[area] && pre_state.time <= 405) {
    if ((pre_state.y_seen[agent] - post_state.y_seen[agent]) == 1 && 
        (pre_state.y_vic[area] - post_state.y_vic[area]) == 1 &&
        (post_state.y_total - pre_state.y_total) == 1 &&
        (post_state.time - pre_state.time) == 15) {
      return 1;
    } 
    return 0;
  }
  else {
    return 0;
  }
}

template <class State> std::optional<State> move(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  if (state.loc[agent] == c_area && state.time <= 590) {
    state.loc[agent] = n_area;
    state.y_seen[agent] = 0;
    state.g_seen[agent] = 0;
    
    if (state.visited[agent].find(n_area) == state.visited[agent].end()) {
      state.visited[agent][n_area] = 1;
      state.seed++;
    }
    else {
      state.visited[agent][n_area] = 1 + state.visited[agent][n_area];
      state.seed++;
    }
    state.time = state.time + 10;

    state.times_searched = 0;

    if (in(n_area,state.left_region)) {
      if (!state.loc_tracker["left"].empty()) {
        state.loc_tracker["left"].pop_back();
      }

      state.left_explored = true;
      for(auto a : state.left_region) {
        if (state.visited[agent].find(a) == state.visited[agent].end()) {
          state.left_explored = false;
          break;
        }
      }
    }
    if (in(n_area,state.right_region)) {
      if (!state.loc_tracker["right"].empty()) {
        state.loc_tracker["right"].pop_back();
      }

      state.right_explored = true;
      for(auto a : state.right_region) {
        if (state.visited[agent].find(a) == state.visited[agent].end()) {
          state.right_explored = false;
          break;
        }
      }
    }
    if (in(n_area,state.mid_region)) {
      if (!state.loc_tracker["mid"].empty()) {
        state.loc_tracker["mid"].pop_back();
      }
      state.mid_explored = true;
      for(auto a : state.mid_region) {
        if (state.visited[agent].find(a) == state.visited[agent].end()) {
          state.mid_explored = false;
          break;
        }
      }
    }

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> double move(State pre_state, State post_state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  if (pre_state.loc[agent] == c_area && pre_state.time <= 590) {
    if (post_state.loc[agent] != n_area) {
      return 0;
    }

    if (post_state.y_seen[agent] != 0 || post_state.g_seen[agent] != 0) {
      return 0;
    }
    
    if (!in(n_area,post_state.visited[agent])) {
      return 0;
    }
    
    if ((post_state.time - pre_state.time) != 10) {
      return 0;
    }

    if ((post_state.times_searched != 0)) {
      return 0;
    }

    return 1;
  }
  else {
    return 0;
  }
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
    {Task("SAR_O", Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks sweep_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_left_O",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks sweep_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_right_O",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks zigzag_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_left_O",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks zigzag_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_right_O",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks explore_left_to_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}),{},{agent})}}; 
}

template <class State> pTasks explore_right_to_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}),{},{agent})}}; 
}

template <class State> pTasks explore_mid_left_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}),{},{agent})}}; 
}

template <class State> pTasks explore_mid_right_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}),{},{agent})}}; 
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
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}}), {"agent","area"},{agent}),
      Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent})}};
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
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
        Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
      Task("explore_left_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent})}};
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
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
        Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
      Task("explore_right_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent})}};
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
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}}), {"agent", "area"},{agent}),
      Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent", "area"},{agent}),
      Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}), {"agent","c_area","n_area"},{agent}),
        Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
      Task("explore_mid_region_O",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
    {Task("SAR_YF", Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks sweep_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_left_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks sweep_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("sweep_right_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks zigzag_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_left_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks zigzag_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25,
    {Task("zigzag_right_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
}

template <class State> pTasks explore_left_to_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}), {},{agent})}}; 
}

template <class State> pTasks explore_right_to_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}),{},{agent})}}; 
}

template <class State> pTasks explore_mid_left_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}),{},{agent})}}; 
}

template <class State> pTasks explore_mid_right_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {1, 
    {Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent}),
     Task("!exit",Args({}), {},{agent})}}; 
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
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}}), {"agent","area"},{agent}),
      Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
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
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}}), {"agent","area"},{agent}),
      Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
        Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}), {"agent","c_area","n_area"},{agent}),
      Task("explore_left_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
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
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
        Task("explore_right_region_YF",Args({{"agent",agent}}), {"agent"},{agent})}}; 
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
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}), {"agent","c_area","n_area"},{agent}),
      Task("explore_right_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!search",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}};
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
      {Task("!triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}}),{"agent","area"},{agent}),
      Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
        {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}),{"agent","c_area","n_area"},{agent}),
        Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
      {Task("!move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}}), {"agent","c_area","n_area"},{agent}),
      Task("explore_mid_region_YF",Args({{"agent",agent}}),{"agent"},{agent})}}; 
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
    std::unordered_map<std::string, std::string> loc;
    std::unordered_map<std::string, int> y_vic;
    std::unordered_map<std::string, int> g_vic;
    int y_total;
    int g_total;
    int y_max;
    int g_max;
    std::unordered_map<std::string, int> y_seen;
    std::unordered_map<std::string, int> g_seen;
    std::vector<std::string> left_region;
    std::vector<std::string> right_region;
    std::vector<std::string> mid_region;
    bool left_explored;
    bool right_explored;
    bool mid_explored;
    int time;
    int times_searched;
    std::unordered_map<std::string, std::vector<std::string>> loc_tracker;
    std::unordered_map<std::string, std::unordered_map<std::string, int>> visited; 
    
    // Not part of the state representation!
    int seed = 100;

    friend bool operator== (SARState & lhs, SARState & rhs) {
      return (
             lhs.loc == rhs.loc && 
             lhs.y_vic == rhs.y_vic &&
             lhs.g_vic == rhs.g_vic &&
             lhs.y_total == rhs.y_total &&
             lhs.g_total == rhs.g_total &&
             lhs.y_seen == rhs.y_seen &&
             lhs.g_seen == rhs.g_seen &&
             lhs.left_region == rhs.left_region &&
             lhs.right_region == rhs.right_region &&
             lhs.mid_region == rhs.mid_region &&
             lhs.time == rhs.time &&
             lhs.visited == rhs.visited &&
             lhs.y_max == rhs.y_max &&
             lhs.g_max == rhs.g_max
          );
    }
    void set_max_vic() {
      g_max = 0;
      for (auto i = g_vic.begin(); i != g_vic.end(); ++i) {
        g_max += i->second;
      }

      y_max = 0;
      for (auto i = y_vic.begin(); i != y_vic.end(); ++i) {
        y_max += i->second;
      }
    }

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
