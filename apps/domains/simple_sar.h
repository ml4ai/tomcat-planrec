#include "../cpphop.h"
#include <math.h>
#include <nlohmann/json.hpp>

using json = nlohmann::ordered_json;


// operators
template <class State> std::optional<State> search(State state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (state.loc[agent] == area && state.time <= 590) {
    if (state.time < 420 && (state.y_vic[area] - state.y_seen[agent]) > 0) {
      state.y_seen[agent] = state.y_seen[agent] + 1;
    }

    if ((state.g_vic[area] - state.g_seen[agent]) > 0) {
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
    if (pre_state.time < 420 && (pre_state.y_vic[area] - pre_state.y_seen[agent]) > 0) {
      if ((post_state.y_seen[agent] - pre_state.y_seen[agent]) != 1) {
        return 0.00;
      } 
    }

    if ((pre_state.g_vic[area] - pre_state.g_seen[agent]) > 0) {
      if ((post_state.g_seen[agent] - pre_state.g_seen[agent]) != 1) {
        return 0.00;
      }
    } 
 
    if ((post_state.time - pre_state.time) != 10) {
      return 0.00;
    } 
    return 1.00;

  }
  else {
    return 0.00;
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

template <class State> double triageGreen(State pre_state,State post_state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (pre_state.loc[agent] == area && post_state.loc[agent] == area && pre_state.g_vic[area] > 0 && pre_state.time <= 593) {
    if ((pre_state.g_seen[agent] - post_state.g_seen[agent]) == 1 && 
        (pre_state.g_vic[agent] - post_state.g_vic[agent]) == 1 &&
        (post_state.g_total - pre_state.g_total) == 1 &&
        (post_state.time - pre_state.time) == 7) {
      return 1.00;
    } 
    return 0.00;
  }
  else {
    return 0.00;
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

template <class State> double triageYellow(State pre_state,State post_state, Args args) {
  auto agent = args["agent"];
  auto area = args["area"];
  if (pre_state.loc[agent] == area && post_state.loc[agent] == area && pre_state.y_vic[area] > 0 && pre_state.time <= 405) {
    if ((pre_state.y_seen[agent] - post_state.y_seen[agent]) == 1 && 
        (pre_state.y_vic[agent] - post_state.y_vic[agent]) == 1 &&
        (post_state.y_total - pre_state.y_total) == 1 &&
        (post_state.time - pre_state.time) == 15) {
      return 1.00;
    } 
    return 0.00;
  }
  else {
    return 0.00;
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
      return 0.00;
    }

    if (post_state.y_seen[agent] != 0 || post_state.g_seen[agent] != 0) {
      return 0.00;
    }
    
    if (post_state.visited[agent] != n_area) {
      return 0.00;
    }
    
    if ((post_state.time - pre_state.time) != 10) {
      return 0.00;
    }

    return 1.00;
  }
  else {
    return 0.00;
  }
}
template <class State> std::optional<State> exit(State state, Args args) {
    return state;
}

template <class State> double exit(State pre_state, State post_state, Args args) {
    return 1.00;
}
// Methods
template <class State> pTasks explore_left_to_right(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_left_region",Args({{"agent",agent}})),
     Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_right_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_right_to_left(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_right_region",Args({{"agent",agent}})),
     Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_left_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_left_right(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_left_region",Args({{"agent",agent}})),
     Task("explore_right_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks explore_mid_right_left(State state, Args args) {
  auto agent = args["agent"];
  return {true, 
    {Task("explore_mid_region",Args({{"agent",agent}})),
     Task("explore_right_region",Args({{"agent",agent}})),
     Task("explore_left_region",Args({{"agent",agent}})),
     Task("exit",Args({}))}}; 
}

template <class State> pTasks search_left(State state, Args args) {
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

template <class State> pTasks triageGreen_left(State state, Args args) {
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

template <class State> pTasks triageYellow_left(State state, Args args) {
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

template <class State> pTasks move_left(State state, Args args) {
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

template <class State> pTasks leave_left(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.left_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
 
  if (state.time > 590 || explored) {
    return {true,{}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> pTasks search_right(State state, Args args) {
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

template <class State> pTasks triageGreen_right(State state, Args args) {
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

template <class State> pTasks triageYellow_right(State state, Args args) {
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

template <class State> pTasks move_right(State state, Args args) {
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

template <class State> pTasks leave_right(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.right_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
 
  if (state.time > 590 || explored) {
    return {true,{}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> pTasks search_mid(State state, Args args) {
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

template <class State> pTasks triageGreen_mid(State state, Args args) {
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

template <class State> pTasks triageYellow_mid(State state, Args args) {
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

template <class State> pTasks move_mid(State state, Args args) {
  auto agent = args["agent"];
  std::string n_area = "none";
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      n_area = a;
      break;
    }
  }
  if (state.time <= 590 && n_area != "none") {
    return {true, 
      {Task("move",Args({{"agent",agent},{"c_area",state.loc[agent]},{"n_area",n_area}})),
      Task("explore_mid_region",Args({{"agent",agent}}))}}; 
  }
  else {
    return {false,{}};
  }
}

template <class State> pTasks leave_mid(State state, Args args) {
  auto agent = args["agent"];
  bool explored = true;
  for(auto a : state.mid_region) {
    if (!in(a,state.visited[agent])) {
      explored = false;
      break;
    }
  }
 
  if (state.time > 590 || explored) {
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
