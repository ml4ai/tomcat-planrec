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
template <class State> pTasks travel_by_foot(State state, Args args) {
    auto x = args["x"];
    auto y = args["y"];
    auto a = args["a"];

    if (state.dist[x][y] <= 2) {
        return {0.50, {Task("walk", Args({{"a", a}, {"x", x}, {"y", y}}))}};
    }
    else {
        return {0.00, {}};
    }
}

template <class State> pTasks travel_by_taxi(State state, Args args) {
    auto a = args["a"];
    auto x = args["x"];
    auto y = args["y"];

    if (state.cash[a] >= taxi_rate(state.dist[x][y])) {
        return {0.50,
                {Task("call_taxi", Args({{"a", a}, {"x", x}})),
                 Task("ride_taxi", Args({{"a", a}, {"x", x}, {"y", y}})),
                 Task("pay_driver", Args({{"a", a}}))}};
    }
    else {
        return {0.00, {}};
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
};

class TravelSelector {


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
    Methods<TravelState> methods = Methods<TravelState>({
        {"travel", {travel_by_foot, travel_by_taxi}},
    });

    TravelDomain() {
        std::cout << "Operators: ";
        print(this->operators);

        std::cout << "Methods: ";
        print(this->methods);
    };
};