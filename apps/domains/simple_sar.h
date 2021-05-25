#include "../cpphop.h"
#include <math.h>
#include <nlohmann/json.hpp>
#include <string>

using json = nlohmann::ordered_json;


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
    
    state.visited[agent].push_back(n_area);
    state.time = state.time + 10;

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
    {Task("SAR_O", Args({{"agent",agent}}))}};
}

template <class State> pTasks explore_left_to_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_right_to_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_left_right_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_right_left_O(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_mid_region_O",Args({{"agent",agent}})),
     Task("explore_right_region_O",Args({{"agent",agent}})),
     Task("explore_left_region_O",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks search_left_O(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
    }
    return {prob, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.475;
    }
    else {
      prob = 0.95;
    }
    return {prob, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.475;
    }
    else {
      prob = 0.95;
    }
    return {prob, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_left_O(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  std::string n_area;
  for(auto a : state.left_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      explored = false;
      break;
    }
  }
  if (state.time <= 590 && !explored) {
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.left_region));
    if (need_to_move) {
      return {1, 
        {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
    }
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
    }
    return {prob, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_left_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_left_O(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.left_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
  
  if (state.time > 590) {
    return {1,{}};
  }

  if (explored) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
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
      prob = 0.025;
    }
    else {
      prob = 0.5;
    }
    return {prob, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.475;
    }
    else {
      prob = 0.95;
    }
    return {prob, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.475;
    }
    else {
      prob = 0.95;
    }
    return {prob, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_right_O(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  std::string n_area;
  for(auto a : state.right_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      explored = false;
      break;
    }
  }
  if (state.time <= 590 && !explored) {
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.right_region));
    if (need_to_move) {
      return {1, 
        {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
    }
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
    }
    return {prob, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_right_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_right_O(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.right_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
  
  if (state.time > 590) {
    return {1,{}};
  }

  if (explored) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
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
      prob = 0.025;
    }
    else {
      prob = 0.5;
    }
    return {prob, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.475;
    }
    else {
      prob = 0.95;
    }
    return {prob, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.475;
    }
    else {
      prob = 0.95;
    }
    return {prob, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_mid_O(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  std::string n_area;
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      explored = false;
      break;
    }
  }
  if (state.time <= 590 && !explored) {
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.mid_region));
    if (need_to_move) {
      return {1, 
        {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
    }
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
    }
    return {prob, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_mid_region_O",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_mid_O(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
  
  if (state.time > 590) {
    return {1,{}};
  }

  if (explored) {
    double prob;
    if (state.g_seen[agent] || (state.y_seen[agent] && state.time <= 405)) {
      prob = 0.025;
    }
    else {
      prob = 0.5;
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

template <class State> pTasks explore_left_to_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_right_to_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_left_right_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_right_left_YF(State state, Args args) {
  auto agent = args["agent"];
  return {0.25, 
    {Task("explore_mid_region_YF",Args({{"agent",agent}})),
     Task("explore_right_region_YF",Args({{"agent",agent}})),
     Task("explore_left_region_YF",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks search_left_YF(State state, Args args) {
  auto agent = args["agent"];
  bool need_to_move = (state.loc[agent] == "entrance" || 
                       !in(state.loc[agent], state.left_region));
  if (state.time <= 590 && !need_to_move) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
          prob = 0.5;
        }
      }
    }
    return {prob, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.95;
    }
    else {
      prob = 0.05/3;
    }
    return {prob, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
    return {0.95, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_left_YF(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  std::string n_area;
  for(auto a : state.left_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      explored = false;
      break;
    }
  }
  if (state.time <= 590 && !explored) {
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.left_region));
    if (need_to_move) {
      return {1, 
        {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
    }
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
          prob = 0.5;
        }
      }
    }
    return {prob, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_left_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_left_YF(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.left_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
  
  if (state.time > 590) {
    return {1,{}};
  }

  if (explored) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
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
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
          prob = 0.5;
        }
      }
    }
    return {prob, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.95;
    }
    else {
      prob = 0.05/3;
    }
    return {prob, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
    return {0.95, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_right_YF(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  std::string n_area;
  for(auto a : state.right_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      explored = false;
      break;
    }
  }
  if (state.time <= 590 && !explored) {
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.right_region));
    if (need_to_move) {
      return {1, 
        {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
    }
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
          prob = 0.5;
        }
      }
    }
    return {prob, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_right_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_right_YF(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.right_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
  
  if (state.time > 590) {
    return {1,{}};
  }

  if (explored) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
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
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
          prob = 0.5;
        }
      }
    }
    return {prob, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
      prob = 0.95;
    }
    else {
      prob = 0.05/3;
    }
    return {prob, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
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
    return {0.95, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks move_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  std::string n_area;
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      explored = false;
      break;
    }
  }
  if (state.time <= 590 && !explored) {
    bool need_to_move = (state.loc[agent] == "entrance" || 
                         !in(state.loc[agent], state.mid_region));
    if (need_to_move) {
      return {1, 
        {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
        Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
    }
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
          prob = 0.5;
        }
      }
    }
    return {prob, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_mid_region_YF",Args({{"agent",agent}}))}}; 
  }
  else {
    return {0,{}};
  }
}

template <class State> pTasks leave_mid_YF(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
  
  if (state.time > 590) {
    return {1,{}};
  }

  if (explored) {
    double prob;
    if (state.y_seen[agent] && state.time <= 405) {
      if (state.g_seen[agent]) {
        prob = 0.05/3;
      }
      else {
        prob = 0.025;
      }
    }
    else {
      if (state.time > 405 && state.g_seen[agent]) {
        prob = 0.025;
      }
      else {
        if (state.g_seen[agent]) {
          prob = (1 - 0.05/3)/2;
        }
        else {
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
    int time;
    std::unordered_map<std::string, std::vector<std::string>> visited; 

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
               {"time",this->time},
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
      Operators<SARState>({{"search",search},
                           {"triageGreen",triageGreen},
                           {"triageYellow",triageYellow},
                           {"move",move},
                           {"exit",exit}});

    pOperators<SARState> poperators = 
      pOperators<SARState>({{"search",search},
                           {"triageGreen",triageGreen},
                           {"triageYellow",triageYellow},
                           {"move",move},
                           {"exit",exit}});


    Methods<SARState> methods =
      Methods<SARState>({{"SAR",
                          {SAR_O,SAR_YF}},
                         {"SAR_O",
                          {explore_left_to_right_O,
                           explore_right_to_left_O,
                           explore_mid_left_right_O,
                           explore_mid_right_left_O}},
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
                          {explore_left_to_right_YF,
                           explore_right_to_left_YF,
                           explore_mid_left_right_YF,
                           explore_mid_right_left_YF}},
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
