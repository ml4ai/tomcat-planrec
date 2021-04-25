#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

using Args = std::unordered_map<std::string, std::string>;

using Task = std::pair<std::string, Args>;
using Tasks = std::vector<Task>;
using bTasks = std::pair<bool, Tasks>;

template <class State>
using Operator = std::optional<State> (*)(State, Args);

template <class State>
using Operators = std::unordered_map<std::string, Operator<State>>;

template <class State> using Method = bTasks (*)(State, Args);

template <class State>
using Methods = std::unordered_map<std::string, std::vector<Method<State>>>;

template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

template <class State> void print(Operators<State> operators) {
    for (auto [operator_name, operator_func] : operators) {
        std::cout << operator_name << ", ";
    }
    std::cout << std::endl;
}

template <class State> void print(Methods<State> methods) {
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

void print(bTasks btasks) { print(btasks.second); }

template <class State>
bTasks seek_plan(State state,
                 std::vector<Task> tasks,
                 bTasks plan,
                 Operators<State> operators,
                 Methods<State> methods,
                 int depth) {
    std::cout << "depth: " << depth << std::endl;
    std::cout << "tasks: ";
    print(tasks);
    std::cout << std::endl;
    if (tasks.size() == 0) {
        return bTasks(true, plan.second);
    }

    Task task = tasks.back();
    if (in(task.first, operators)) {
        auto op = operators[task.first];
        std::optional<State> newstate = op(state, task.second);
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

template <class State>
bTasks pyhop(State state,
             Tasks tasks,
             Operators<State> operators,
             Methods<State> methods) {
    bTasks result = seek_plan(state, tasks, {}, operators, methods, 0);
    print(result);
    return result;
}
