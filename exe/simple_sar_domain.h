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
      if (y_vic > state.y_vic[area]) {
        y_vic = state.y_vic[area];
      }
      state.y_seen[agent] = state.y_seen[agent] + y_vic;
    }
    else {
      state.y_seen[agent] = 0;
    }
 
    std::poisson_distribution<int> g_dist(state.g_vic[area]/2);

    int g_vic = g_dist(gen);

    if (g_vic > state.g_vic[area]) {
      g_vic = state.g_vic[area];
    }

    state.g_seen[agent] = state.g_seen[agent] + g_vic;


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
    state.loc[agent] = n_area;
    state.y_seen[agent] = 0;
    state.g_seen[agent] = 0;
    
    state.visited["me"].push_back(n_area);
    state.time = state.time + 10;

    return state;
  }
  else {
    return std::nullopt;
  }
}

template <class State> std::optional<State> exit(State state, Args args) {
    return state;
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
  std::string n_area = "none";
  for(auto a : state.left_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      break;
    }
  }
  if (state.time <= 590 && n_area != "none") {
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
  if (state.time > 590 || state.left_region.empty()) {
    return {true,{}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks search_right(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region",Args({{"agent",agent}}))}};
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks triageGreen_right(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && state.g_seen[agent] > 0 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks triageYellow_right(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 405 && state.y_seen[agent] > 0 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_right_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks move_right(State state, Args args) {
  auto agent = args["agent"];
  std::string n_area = "none";
  for(auto a : state.right_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      break;
    }
  }
  if (state.time <= 590 && n_area != "none") {
    return {true, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_right_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks leave_right(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590 || state.right_region.empty()) {
    return {true,{}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks search_mid(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("search",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region",Args({{"agent",agent}}))}};
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks triageGreen_mid(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 590 && state.g_seen[agent] > 0 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("triageGreen",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks triageYellow_mid(State state, Args args) {
  auto agent = args["agent"];
  if (state.time <= 405 && state.y_seen[agent] > 0 && state.loc[agent] != "entrance") {
    return {true, 
      {Task("triageYellow",Args({{"agent",agent},{"area",state.loc[agent]}})),
      Task("explore_mid_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks move_mid(State state, Args args) {
  auto agent = args["agent"];
  std::string n_area = "none";
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      break;
    }
  }
  if (state.time <= 590 && n_area != "none") {
    std::string n_area = state.mid_region.back();
    state.mid_region.pop_back();
    return {true, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_mid_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> bTasks leave_mid(State state, Args args) {
  auto agent = args["agent"];
  if (state.time > 590 || state.mid_region.empty()) {
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
    int y_total;
    int g_total;
    std::unordered_map<std::string, int> y_seen;
    std::unordered_map<std::string, int> g_seen;
    std::vector<std::string> left_region;
    std::vector<std::string> right_region;
    std::vector<std::string> mid_region;
    int time;
    std::unordered_map<std::string, std::vector<std::string>> visited; 
};

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
                           explore_mid_right_left}},
                         {"explore_left_region",
                          {search_left,
                           triageYellow_left,
                           triageGreen_left,
                           move_left,
                           leave_left}},
                         {"explore_right_region",
                          {search_right,
                           triageYellow_right,
                           triageGreen_right,
                           move_right,
                           leave_right}},
                         {"explore_mid_region",
                          {search_mid,
                           triageYellow_mid,
                           triageGreen_mid,
                           move_mid,
                           leave_mid}}});

    SARDomain() {
      std::cout << "Operators: ";
      print(this->operators);

      std::cout << "Method: ";
      print(this->methods);
    };
};
