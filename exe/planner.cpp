#include <any>
#include <iostream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <variant>
#include <vector>

using namespace std;

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

variant<State, bool> walk(State state, string a, string x, string y) {
    cout << "FLAG" << endl;
    if (state.loc[a] == x) {
        state.loc[a] = y;
        return state;
    }
    else {
        return false;
    }
}

auto walk_op = Operator("walk", function(walk));

variant<State, bool> call_taxi(State state, string a, string x) {
    state.loc["taxi"] = x;
    return state;
}

auto call_taxi_op = Operator("call_taxi", function(call_taxi));

variant<State, bool> ride_taxi(State state, string a, string x, string y) {
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

auto ride_taxi_op = Operator("ride_taxi", function(ride_taxi));

variant<State, bool> pay_driver(State state, string a) {
    if (state.cash[a] >= state.owe[a]) {
        state.cash[a] = state.cash[a] - state.owe[a];
        state.owe[a] = 0;
        return state;
    }
    else {
        return false;
    }
}

auto pay_driver_op = Operator("pay_driver", function(pay_driver));

// Methods
vector<vector<string>>
travel_by_foot(State state, string a, string x, string y) {
    if (state.dist[x][y] <= 2) {
        return {{"walk", a, x, y}};
    }
    else {
        return {{}};
    }
}

vector<vector<string>>
travel_by_taxi(State state, string a, string x, string y) {
    if (state.cash[a] >= taxi_rate(state.dist[x][y])) {
        return {{"call_taxi", a, x}, {"ride_taxi", a, x, y}, {"pay_driver", a}};
    }
    else {
        return {{}};
    }
}

// auto operators = unordered_map<string, any>({"walk", walk});

// void expand(Operator op) {

//}

// void expand(Method m) {

//}

variant<vector<any>, bool> seek_plan(State state,
                                     vector<vector<string>> tasks,
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
    }
}

variant<vector<any>, bool> pyhop(State state,
                                 vector<vector<string>> tasks,
                                 unordered_map<string, any> ops,
                                 unordered_map<string, any> methods) {
    auto result = seek_plan(state, tasks, {}, ops, methods, 0);
    return result;
}

int main(int argc, char* argv[]) {
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
