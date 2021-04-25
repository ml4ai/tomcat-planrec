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

template <class State> using Operator = std::optional<State> (*)(State, Args);

template <class State>
using Operators = std::unordered_map<std::string, Operator<State>>;

template <class State> using Method = bTasks (*)(State, Args);

template <class State>
using Methods = std::unordered_map<std::string, std::vector<Method<State>>>;

// Utility method to see if an element is in an associative container
template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

// Utility methods for printing information to stdout.
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
        std::cout << "[";
    for (auto task : tasks) {
        std::cout << "(";
        std::cout << task.first << ",";
        for (auto [k, v] : task.second) {
            std::cout << v << ",";
        }
        std::cout << ")";
    }
    std::cout << "]";
    std::cout << std::endl;
}

void print(bTasks btasks) { print(btasks.second); }

template <class State, class Domain>
bTasks seek_plan(State state,
                 std::vector<Task> tasks,
                 bTasks plan,
                 Domain domain,
                 int depth) {
    std::cout << "depth: " << depth << std::endl;
    std::cout << "tasks: ";
    print(tasks);
    std::cout << std::endl;
    if (tasks.size() == 0) {
        return bTasks(true, plan.second);
    }

    Task task = tasks.back();
    if (in(task.first, domain.operators)) {
        auto op = domain.operators[task.first];
        std::optional<State> newstate = op(state, task.second);
        if (newstate) {
            tasks.pop_back();
            plan.second.push_back(task);
            bTasks solution = seek_plan(
                newstate.value(), tasks, plan, domain, depth + 1);
            if (solution.first) {
                return solution;
            }
        }
        return {false, {}};
    }

    if (in(task.first, domain.methods)) {
        auto relevant = domain.methods[task.first];
        for (auto method : relevant) {
            auto subtasks = method(state, task.second);
            if (subtasks.first) {
                tasks.pop_back();
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    tasks.push_back(*(--i));
                }
                bTasks solution = seek_plan(
                    state, tasks, plan, domain, depth + 1);
                if (solution.first) {
                    return solution;
                }
            }
        }
        return {false, {}};
    }
}

template <class State, class Domain>
bTasks cpphop(State state,
             Tasks tasks,
             Domain domain) {
    bTasks result = seek_plan(state, tasks, {}, domain, 0);
    print(result);
    return result;
}
