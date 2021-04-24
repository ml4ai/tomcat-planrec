#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

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

using Args = unordered_map<string, string>;
using bState = optional<State>;
using Task = pair<string, Args>;
using Tasks = vector<Task>;
using bTasks = pair<bool, Tasks>;
using Ptr2Operator = bState (*)(State, Args);
using Operators = unordered_map<string, Ptr2Operator>;
using Ptr2Method = bTasks (*)(State, Args);
using Methods = unordered_map<string, vector<Ptr2Method>>;

template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

template <class... Types> class Operator {
  public:
    string name;
    function<Types...> func;
    Operator(string name, function<Types...> func) : name(name), func(func){};

    template <class... Ts> bState operator()(Ts... args) {
        return this->func(args...);
    }
};

auto taxi_rate(double dist) { return 1.5 + 0.5 * dist; }

// Operators

bState walk(State state, Args args) {
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

bState call_taxi(State state, Args args) {
    state.loc["taxi"] = args["x"];
    return state;
}

bState ride_taxi(State state, Args args) {
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

bState pay_driver(State state, Args args) {
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

bTasks seek_plan(State state,
                 vector<Task> tasks,
                 bTasks plan,
                 Operators operators,
                 Methods methods,
                 int depth) {
    if (tasks.size() == 0) {
        return bTasks(true, plan.second);
    }
    Task task = tasks.back();
    if (in(task.first, operators)) {
        auto op = operators[task.first];
        bState newstate = op(state, task.second);
        if (newstate) {
            tasks.pop_back();
            plan.second.push_back(task);
            bTasks solution = seek_plan(
                newstate.value(), tasks, plan, operators, methods, depth + 1);
            if (solution.first) {
                return solution;
            }
        }
        return {false, {}};
    }

    if (in(task.first, methods)) {
        auto relevant = methods[task.first];
        for (auto method : relevant) {
            auto subtasks = method(state, task.second);
        }
    }
}

bTasks
pyhop(State state, vector<Task> tasks, Operators operators, Methods methods) {
    auto result = seek_plan(state, tasks, {}, operators, methods, 0);
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
    Operators operators = {};
    operators["walk"] = walk;
    operators["ride_taxi"] = ride_taxi;
    operators["call_taxi"] = call_taxi;
    operators["pay_driver"] = pay_driver;

    // Declare methods
    Methods methods = {};
    methods["travel"] = {travel_by_foot, travel_by_taxi};

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}))}};
    pyhop(state1, tasks, operators, methods);
    return EXIT_SUCCESS;
}
