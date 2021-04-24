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

void print(Operators operators) {
    for (auto [operator_name, operator_func] : operators) {
        cout << operator_name << ", ";
    }
    cout << endl;
}

void print(Methods methods) {
    for (auto [method_name, method_func] : methods) {
        cout << method_name << ", ";
    }
    cout << endl;
}

void print(Tasks tasks) {
    for (auto task : tasks) {
        cout << task.first << ", ";
    }
    cout << endl;
}

void print(bTasks btasks) {
    print(btasks.second);
}


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
    cout << "depth:" << depth << endl;
    cout << "tasks:" << endl;
    print(tasks);
    cout << endl;
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
            if (subtasks.first) {
                tasks.pop_back();
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    tasks.push_back(*(--i));
                }
                bTasks solution = seek_plan(
                    state, tasks, plan, operators, methods, depth + 1);
                if (solution.first) {
                    return solution;
                }
            }
        }
        return {false, {}};
    }
}

bTasks pyhop(State state, Tasks tasks, Operators operators, Methods methods) {
    auto result = seek_plan(state, tasks, {}, operators, methods, 0);
    print(result);
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

    cout << "Operators: ";
    print(operators);

    // Declare methods
    Methods methods = {};
    methods["travel"] = {travel_by_foot, travel_by_taxi};
    cout << "Methods: ";
    print(methods);

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}))}};
    pyhop(state1, tasks, operators, methods);
    return EXIT_SUCCESS;
}
