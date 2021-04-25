#include "cpphop.h"

using namespace std;


auto taxi_rate(double dist) { return 1.5 + 0.5 * dist; }

// Operators

template <class State>
std::optional<State> walk(State state, Args args) {
    auto a = args["a"];
    auto x = args["x"];
    auto y = args["y"];
    if (state.loc[a] == x) {
        state.loc[a] = y;
        return state;
    }
    else {
        return nullopt;
    }
}

template <class State>
std::optional<State> call_taxi(State state, Args args) {
    state.loc["taxi"] = args["x"];
    return state;
}

template <class State>
std::optional<State> ride_taxi(State state, Args args) {
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
        return nullopt;
    }
}

template <class State>
std::optional<State> pay_driver(State state, Args args) {
    auto a = args["a"];
    if (state.cash[a] >= state.owe[a]) {
        state.cash[a] = state.cash[a] - state.owe[a];
        state.owe[a] = 0;
        return state;
    }
    else {
        return nullopt;
    }
}

// Methods
template <class State>
bTasks travel_by_foot(State state, Args args) {
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

template <class State>
bTasks travel_by_taxi(State state, Args args) {
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

int main(int argc, char* argv[]) {
    auto state1 = TravelState("state1");
    state1.loc["me"] = "home";
    state1.cash["me"] = 20;
    state1.owe["me"] = 0;
    state1.dist["home"]["park"] = 8;
    state1.dist["park"]["home"] = 8;

    // Declare operators
    Operators<TravelState> operators = {};
    operators["walk"] = walk;
    operators["ride_taxi"] = ride_taxi;
    operators["call_taxi"] = call_taxi;
    operators["pay_driver"] = pay_driver;

    cout << "Operators: ";
    print(operators);

    // Declare methods
    Methods<TravelState> methods = {};
    methods["travel"] = {travel_by_foot, travel_by_taxi};
    cout << "Methods: ";
    print(methods);

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}))}};
    pyhop(state1, tasks, operators, methods);
    return EXIT_SUCCESS;
}
