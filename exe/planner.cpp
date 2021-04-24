#include <any>
#include <iostream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <variant>
#include <vector>
#include <optional>

using namespace std;

typedef unordered_map<string, string> Args;

template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
  return container.count(element);
}

class State {
public:
  State(string name) : name(name){};
  string name;
  unordered_map<string, string> loc;
  unordered_map<string, unordered_map<string, double>> dist;
  unordered_map<string, double> owe;
  unordered_map<string, double> cash;
};

template <class... Types> class Operator {
public:
  string name;
  function<Types...> func;
  Operator(string name, function<Types...> func) : name(name), func(func){};

  template <class... Ts> variant<State, bool> operator()(Ts... args) {
    return this->func(args...);
  }
};

auto taxi_rate(double dist) { return 1.5 + 0.5 * dist; }

// Operators

variant<State, bool> walk(State state, Args args) {
  auto a = args["a"];
  auto x = args["x"];
  auto y = args["y"];
  if (state.loc[a] == x) {
    state.loc[a] = y;
    return state;
  } else {
    return false;
  }
}

variant<State, bool> call_taxi(State state, Args args) {
  state.loc["taxi"] = args["x"];
  return state;
}

variant<State, bool> ride_taxi(State state, Args args) {
  auto x = args["x"];
  auto y = args["y"];
  auto a = args["a"];
  if (state.loc["taxi"] == x and state.loc[a] == x) {
    state.loc["taxi"] = y;
    state.loc[a] = y;
    state.owe[a] = taxi_rate(state.dist[x][y]);
    return state;
  } else {
    return false;
  }
}

variant<State, bool> pay_driver(State state, Args args) {
  auto a = args["a"];
  if (state.cash[a] >= state.owe[a]) {
    state.cash[a] = state.cash[a] - state.owe[a];
    state.owe[a] = 0;
    return state;
  } else {
    return false;
  }
}

// Methods
vector<pair<string, Args>> travel_by_foot(State state, Args args) {
  auto x = args["x"];
  auto y = args["y"];
  auto a = args["a"];

  if (state.dist[x][y] <= 2) {
    return {pair("walk", Args({{"a", a}, {"x", x}, {"y", y}}))};
  }
  else {
    return {pair("", Args())};
  }
}

vector<pair<string, Args>> travel_by_taxi(State state, Args args) {
  auto a = args["a"];
  auto x = args["x"];
  auto y = args["y"];

  if (state.cash[a] >= taxi_rate(state.dist[x][y])) {
    return {pair("call_taxi", Args({{"a", a}, {"x", x}})),
            pair("ride_taxi", Args({{"a", a}, {"x", x}, {"y", y}})),
            pair("pay_driver", Args({{"a", a}}))};
  }
  else {
    return {pair("", Args())};
  }
}

variant<vector<any>, bool> seek_plan(State state, vector<vector<string>> tasks,
                                     vector<any> plan,
                                     unordered_map<string, any> operators,
                                     unordered_map<string, any> methods,
                                     int depth) {
  if (tasks.size() == 0) {
    return plan;
  }
  auto task1 = tasks[0];
  if (in(task1[0], operators)) {
    auto op = operators[task1[0]];
    auto newstate =
  }
}

variant<vector<any>, bool> pyhop(State state, vector<vector<string>> tasks,
                                 unordered_map<string, any> ops,
                                 unordered_map<string, any> methods) {
  auto result = seek_plan(state, tasks, {}, ops, methods, 0);
  return result;
}

int main(int argc, char *argv[]) {
  State state1 = State("state1");
  state1.loc["me"] = "home";
  state1.cash["me"] = 20;
  state1.owe["me"] = 0;
  state1.dist["home"]["park"] = 8;
  state1.dist["park"]["home"] = 8;

  // Declare operators
  unordered_map<string, any> operators = {};
  operators["walk"] = walk;
  operators["ride_taxi"] = ride_taxi;
  operators["call_taxi"] = call_taxi;
  operators["pay_driver"] = pay_driver;

  // Declare methods
  unordered_map<string, any> methods = {};
  methods["travel"] = vector<any>({travel_by_foot, travel_by_taxi});

  vector<vector<string>> tasks = {{"travel", "me", "home", "park"}};
  pyhop(state1, tasks, operators, methods);
  return EXIT_SUCCESS;
}
