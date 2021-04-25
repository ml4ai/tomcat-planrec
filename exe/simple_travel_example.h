#include "cpphop.h"

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
template <class State> bTasks travel_by_foot(State state, Args args) {
    auto x = args["x"];
    auto y = args["y"];
    auto a = args["a"];

    if (state.dist[x][y] <= 2) {
        return {true, {Task("walk", Args({{"a", a}, {"x", x}, {"y", y}}))}};
    }
    else {
        return {false, {}};
    }
}

template <class State> bTasks travel_by_taxi(State state, Args args) {
    auto a = args["a"];
    auto x = args["x"];
    auto y = args["y"];

    if (state.cash[a] >= taxi_rate(state.dist[x][y])) {
        return {true,
                {Task("call_taxi", Args({{"a", a}, {"x", x}})),
                 Task("ride_taxi", Args({{"a", a}, {"x", x}, {"y", y}})),
                 Task("pay_driver", Args({{"a", a}}))}};
    }
    else {
        return {false, {}};
    }
}

class TravelState {
  public:
    TravelState(std::string name) : name(name){};
    std::string name;
    std::unordered_map<std::string, std::string> loc;
    std::unordered_map<std::string, std::unordered_map<std::string, double>>
        dist;
    std::unordered_map<std::string, double> owe;
    std::unordered_map<std::string, double> cash;
};

template <class State> class TravelDomain {
  public:
    Operators<State> operators = {};
    Methods<State> methods = {};

    TravelDomain() {
        // Declare operators
        this->operators["walk"] = walk;
        this->operators["ride_taxi"] = ride_taxi;
        this->operators["call_taxi"] = call_taxi;
        this->operators["pay_driver"] = pay_driver;

        std::cout << "Operators: ";
        print(this->operators);

        // Declare methods
        this->methods["travel"] = {travel_by_foot, travel_by_taxi};
        std::cout << "Methods: ";
        print(this->methods);
    };
};
