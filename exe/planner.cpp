#include <any>
#include <iostream>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>
#include <tuple>

using namespace std;

class State {
  public:
    State(string name) : name(name){};
    string name;
    unordered_map<string, string> loc;
    unordered_map<string, unordered_map<string, double>> dist;
    unordered_map<string, double> owe;
    unordered_map<string, double> cash;
};

template<class... Types> class Operator {
    public:
        string name;
        function<Types...> func;
        Operator(string name, function<Types...> func) : name(name), func(func) {};

        template<class ...Ts>
        variant<State, bool> operator()(Ts ...args) {
            return this->func(args...);
        }
};


auto taxi_rate(double dist) { return 1.5 + 0.5 * dist; }

// Operators
variant<State, bool> walk(State& state, string a, string x, string y) {
    cout << "FLAG" << endl;
    if (state.loc[a] == x) {
        state.loc[a] = y;
        return state;
    }
    else {
        return false;
    }
}

State call_taxi(State& state, string a, string x) {
    state.loc["taxi"] = x;
    return state;
}

variant<State, bool> ride_taxi(State& state, string a, string x, string y) {
    if (state.loc["taxi"] == x and state.loc[a] == x) {
        state.loc["taxi"] = y;
        state.loc[a] = y;
        state.owe[a] = taxi_rate(state.dist[x][y]);
        return state;
    }
    else {
        return false;
    }
}

variant<State, bool> pay_driver(State& state, string a) {
    if (state.cash[a] >= state.owe[a]) {
        state.cash[a] = state.cash[a] - state.owe[a];
        state.owe[a] = 0;
        return state;
    }
    else {
        return false;
    }
}

// Methods
variant<tuple<any>, bool>
travel_by_foot(State& state, string a, string x, string y) {
    if (state.dist[x][y] <= 2) {
        return make_tuple(make_tuple(&walk, a, x, y));
    }
    else {
        return false;
    }
}

variant<tuple<any>, bool>
travel_by_taxi(State& state, string a, string x, string y) {
    if (state.cash[a] >= taxi_rate(state.dist[x][y])) {
        return make_tuple(make_tuple(&call_taxi, a, x),
                          make_tuple(&ride_taxi, a, x, y),
                          make_tuple(&pay_driver, a));
    }
    else {
        return false;
    }
}

//auto operators = unordered_map<string, any>({"walk", walk});


variant<vector<any>, bool>
seek_plan(State& state, vector<vector<string>> tasks, vector<any> plan, int depth) {
    if (tasks.size() == 0) {
        return plan;
    }
    auto task1 = tasks[0];
}

variant<vector<any>, bool> pyhop(State& state, vector<vector<string>> tasks) {
    auto result = seek_plan(state, tasks, {}, 0);
    return result;
}

int main(int argc, char* argv[]) {
    State state1 = State("state1");
    state1.loc["me"] = "home";
    state1.cash["me"] = 20;
    state1.owe["me"] = 0;
    state1.dist["home"]["park"] = 8;
    state1.dist["park"]["home"] = 8;
    // Declare methods
    unordered_map<string, any> methods = {};
    methods["travel"] = make_tuple(&travel_by_foot, &travel_by_taxi);
    vector<vector<string>> tasks = {{"travel", "me", "home", "park"}};
    auto op1 = Operator("op1", function(walk));
    op1(state1, "me", "park", "home");
    //pyhop(state1, tasks);
    return EXIT_SUCCESS;
}
