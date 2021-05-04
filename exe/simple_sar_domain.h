#include "cpphop.h"
#include <random>

std::default_random_engine gen;

// operators
template <class State> std::optional<State> search(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.loc[agent] == area && state.time <= 590) {
    if (state.time < 420) {
      std::poisson_distribution<int> y_dist(state.y_vic[area]/2);
      int y_vic = y_dist(gen);
      if y_vic > state.y_vic[area] {
        y_vic = state.y_vic[area];
      }
      state.y_seen[agent] = state.y_seen[agent] + y_vic;
    }
    else {
      state.y_seen[agent] = 0;
    }
 
    std::poisson_distribution<int> g_dist(state.g_vic[area]/2);

    int g_vic = g_dist(gen);

    if g_vic > state.g_vic[area] {
      g_vic = state.g_vic[area];
    }

    state.g_seen[agent] = state.g_seen[agent] + g_vic;

    state.searched[agent] = true;

    state.time = state.time + 10;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> std::optional<State> triageGreen(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.loc[agent] == area && state.g_vic[area] > 0 && state.time <= 593) {
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

template <class State> std::optional<State> triageYellow(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.loc[agent] == area && state.y_vic[area] > 0 && state.time <= 405) {
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

template <class State> std::optional<State> move(State state, Args args) {
  auto agent = args["agent"];
  auto c_area = args["c_area"];
  auto n_area = args["n_area"];
  if (state.loc[agent] == c_area && state.time <= 590) {
    state.y_seen[agent] = 0;
    state.g_seen[agent] = 0;

    state.searched[agent] = false;

    state.time = state.time + 10;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> std::optional<State> exit(State state, Args args) {
  if (state.time >= 600) {
    return state;
  }
  else {
    return std::nullopt;
  }
}

// Methods
template <class State> bTasks explore_left_to_right(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_left_region",Args({{"agent",agent}})),
     Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_right_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> bTasks explore_right_to_left(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_right_region",Args({{"agent",agent}})),
     Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_left_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> bTasks explore_mid_left_right(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_left_region",Args({{"agent",agent}})),
     Task("explore_right_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> bTasks explore_mid_right_left(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_right_region",Args({{"agent",agent}})),
     Task("explore_left_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> bTasks search_left(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region",Args({{"agent",agent}}))}};
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks triageGreen_left(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && state.g_seen[agent] > 0 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks triageYellow_left(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 405 && state.y_seen[agent] > 0 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_left_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks move_left(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && !state.left_region.empty()) {
    std::string n_area = state.left_region.back();
    state.left_region.pop_back();
    return {true, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_left_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks leave_left(State state, Args args) {
  auto agent = args["agent"];
  if (state.time >= 590 || state.left_region.empty()) {
    return {true,{}}; 
  }
  else {
    return {false,{}};
  }
}

class SARState {
  public:
    std::unordered_map<std::string, std::string> loc;
    std::unordered_map<std::string, int> y_vic;
    std::unordered_map<std::string, int> g_vic;
    std::unordered_map<std::string, int> y_total;
    std::unordered_map<std::string, int> g_total;
    std::unordered_map<std::string, int> y_seen;
    std::unordered_map<std::string, int> g_seen;
    std::unordered_map<std::string, bool> searched;
    std::unordered_map<std::string, std::string> areas;
    std::vector<std::string> left_region;
    std::vector<std::string> right_region;
    std::vector<std::string> mid_region;
    int time;
}

class SARDomain {
  public:
    Operators<SARState> operators = 
      Operators<SARState>({{"search",search},
                           {"triageGreen",triageGreen},
                           {"triageYellow",triageYellow},
                           {"move",move},
                           {"exit",exit}});

    Methods<SARState> methods =
      Methods<SARState>({{"SAR",
                          {explore_left_to_right,
                           explore_right_to_left,
                           explore_mid_left_right,
                           explore_mid_right_left}}}); 
}
