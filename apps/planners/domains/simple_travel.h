#include "cppMCTShop.h"
#include "typedefs.h"
#include <math.h>
#include <nlohmann/json.hpp>
#include <string>
#include <algorithm>

auto taxi_rate(double dist) { return 1.5 + 0.5 * dist; }

// Operators

template <class State> std::optional<State> walk(State state, Args args) {
    auto a = args["a"];
    auto x = args["x"];
    auto y = args["y"];
    if (state.loc[a] == x) {
        state.loc[a] = y;
        return state;
    }
    else {
        return std::nullopt;
    }
}

template <class State> std::optional<State> call_taxi(State state, Args args) {
    state.loc["taxi"] = args["x"];
    return state;
}

template <class State> std::optional<State> ride_taxi(State state, Args args) {
    auto x = args["x"];
    auto y = args["y"];
    auto a = args["a"];
    if (state.loc["taxi"] == x and state.loc[a] == x) {
        state.loc["taxi"] = y;
        state.loc[a] = y;
        state.owe[a] = taxi_rate(state.dist[x][y]);
        return state;
    }
    else {
        return std::nullopt;
    }
}

template <class State> std::optional<State> pay_driver(State state, Args args) {
    auto a = args["a"];
    if (state.cash[a] >= state.owe[a]) {
        state.cash[a] = state.cash[a] - state.owe[a];
        state.owe[a] = 0;
        return state;
    }
    else {
        return std::nullopt;
    }
}

// Methods
template <class State> cTasks travel_by_foot(State state, Args args) {
    auto x = args["x"];
    auto y = args["y"];
    auto a = args["a"];

    if (state.dist[x][y] <= 2) {
        return {"PASS", {Task("walk", Args({{"a", a}, {"x", x}, {"y", y}}), {"a", "x", "y"},{a})}};
    }
    else {
        return {"NIL", {}};
    }
}

template <class State> cTasks travel_by_taxi(State state, Args args) {
    auto a = args["a"];
    auto x = args["x"];
    auto y = args["y"];

    if (state.cash[a] >= taxi_rate(state.dist[x][y])) {
        return {"PASS",
                {Task("call_taxi", Args({{"a", a}, {"x", x}}),{"a","x"},{a}),
                 Task("ride_taxi", Args({{"a", a}, {"x", x}, {"y", y}}),{"a","x","y"},{a}),
                 Task("pay_driver", Args({{"a", a}}), {"a"},{a})}};
    }
    else {
        return {"NIL", {}};
    }
}

class TravelState {
  public:
    TravelState() = default;
    TravelState(std::string name) : name(name){};
    std::string name;
    std::unordered_map<std::string, std::string> loc;
    std::unordered_map<std::string, std::unordered_map<std::string, double>>
        dist;
    std::unordered_map<std::string, double> owe;
    std::unordered_map<std::string, double> cash;

    nlohmann::json to_json() {
      return nlohmann::json{{"loc", this->loc},
                            {"dist", this->dist},
                            {"owe", this->owe},
                            {"cash", this->cash}};
    }
};

class TravelDomain {
  public:
    // Declare operators
    Operators<TravelState> operators =
        Operators<TravelState>({{"walk", walk},
                                {"call_taxi", call_taxi},
                                {"ride_taxi", ride_taxi},
                                {"pay_driver", pay_driver}});

    // Declare methods
    cMethods<TravelState> cmethods = cMethods<TravelState>({
        {"travel", {travel_by_foot, travel_by_taxi}},
    });
    
    int score(TravelState s) {
      if (s.loc["me"] == "park") {
        return 1*(s.cash["me"]/20.0);
      }
      else {
        return 0;
      }
    } 
    TravelDomain() {
        std::cout << "Operators: ";
        print(this->operators);

        std::cout << "Methods: ";
        print(this->cmethods);
    };
};
