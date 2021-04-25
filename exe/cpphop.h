#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

class State {
  public:
    State(std::string name) : name(name){};
    std::string name;
    std::unordered_map<std::string, std::string> loc;
    std::unordered_map<std::string, std::unordered_map<std::string, double>> dist;
    std::unordered_map<std::string, double> owe;
    std::unordered_map<std::string, double> cash;
};

using Args = std::unordered_map<std::string, std::string>;
using bState = std::optional<State>;
using Task = std::pair<std::string, Args>;
using Tasks = std::vector<Task>;
using bTasks = std::pair<bool, Tasks>;
using Ptr2Operator = bState (*)(State, Args);
using Operators = std::unordered_map<std::string, Ptr2Operator>;
using Ptr2Method = bTasks (*)(State, Args);
using Methods = std::unordered_map<std::string, std::vector<Ptr2Method>>;

template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

void print(Operators operators) {
    for (auto [operator_name, operator_func] : operators) {
        std::cout << operator_name << ", ";
    }
    std::cout << std::endl;
}

void print(Methods methods) {
    for (auto [method_name, method_func] : methods) {
        std::cout << method_name << ", ";
    }
    std::cout << std::endl;
}

void print(Tasks tasks) {
    for (auto task : tasks) {
        std::cout << task.first << ", ";
    }
    std::cout << std::endl;
}

void print(bTasks btasks) {
    print(btasks.second);
}

bTasks seek_plan(State state,
                 std::vector<Task> tasks,
                 bTasks plan,
                 Operators operators,
                 Methods methods,
                 int depth) {
    std::cout << "depth:" << depth << std::endl;
    std::cout << "tasks:" << std::endl;
    print(tasks);
    std::cout << std::endl;
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

