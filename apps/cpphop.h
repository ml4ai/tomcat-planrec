#pragma once

#include "Node.hpp"
#include "Tree.hpp"
#include "util.h"
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

// Utility method to see if an element is in a vector
template <class Element> bool in(Element element, std::vector<Element> v) {
    return std::count(v.begin(), v.end(), element);
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

void print(Plans plans) {
    std::cout << "Plans Found:" << std::endl;
    int i = 0;
    for (auto bt : plans) {
        std::cout << "Plan " << i << ": ";
        print(bt);
        i++;
    }
}

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
    auto [task_id, args] = task;

    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(state, args);
        if (newstate) {
            tasks.pop_back();
            plan.second.push_back(task);
            bTasks solution =
                seek_plan(newstate.value(), tasks, plan, domain, depth + 1);
            if (solution.first) {
                return solution;
            }
        }
        return {false, {}};
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        for (auto method : relevant) {
            auto subtasks = method(state, args);
            if (subtasks.first) {
                tasks.pop_back();
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    tasks.push_back(*(--i));
                }
                bTasks solution =
                    seek_plan(state, tasks, plan, domain, depth + 1);
                if (solution.first) {
                    return solution;
                }
            }
        }
        return {false, {}};
    }
}

template <class State, class Domain, class Selector>
Tree<State, Selector>
seek_planDFS(Tree<State, Selector> t, int v, Domain domain) {
    std::cout << "depth: " << t[v].depth << std::endl;
    std::cout << "tasks: ";
    print(t[v].tasks);
    std::cout << std::endl;
    if (t[v].tasks.size() == 0) {
        t[boost::graph_bundle].plans.push_back(t[v].plan);
        std::cout << "Plan found at depth " << t[v].depth << ":" << std::endl;
        print(t[v].plan);
        std::cout << std::endl;
        return t;
    }

    Task task = t[v].tasks.back();
    auto [task_id, args] = task;

    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(t[v].state, args);
        if (newstate) {
            Node<State, Selector> n;
            n.state = newstate.value();
            n.tasks = t[v].tasks;
            n.tasks.pop_back();
            n.depth = t[v].depth + 1;
            n.plan = t[v].plan;
            n.plan.second.push_back(task);
            int w = boost::add_vertex(n, t);
            boost::add_edge(v, w, t);
            return seek_planDFS(t, w, domain);
        }
        std::cout << "Action Preconditions Failed at depth " << t[v].depth
                  << ", BackTracking!" << std::endl;
        return t;
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        for (auto method : relevant) {
            auto subtasks = method(t[v].state, args);
            if (subtasks.first) {
                Node<State, Selector> n;
                n.state = t[v].state;
                n.tasks = t[v].tasks;
                n.tasks.pop_back();
                n.depth = t[v].depth + 1;
                n.plan = t[v].plan;
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    n.tasks.push_back(*(--i));
                }
                int w = boost::add_vertex(n, t);
                boost::add_edge(v, w, t);
                t = seek_planDFS(t, w, domain);
            }
        }
        return t;
    }
}

template <class State, class Domain>
bTasks cpphop(State state, Tasks tasks, Domain domain) {
    bTasks result = seek_plan(state, tasks, {}, domain, 0);
    print(result);
    return result;
}

template <class State, class Domain, class Selector>
Plans cpphopDFS(State state, Tasks tasks, Domain domain, Selector selector) {
    Tree<State, Selector> t;
    Node<State, Selector> root;
    root.state = state;
    root.tasks = tasks;
    root.plan = {};
    root.depth = 0;
    int v = boost::add_vertex(root, t);
    t = seek_planDFS(t, v, domain);
    print(t[boost::graph_bundle].plans);
    return t[boost::graph_bundle].plans;
}

// MCTS algorithms
// See Tree.hpp for why boost::edges are not used and why
// the successor/predecessor functions are not used
template <class State, class Selector>
std::pair<Tree<State, Selector>, int>
selection(Tree<State, Selector> t, int v, double c, int r_l, int r_t) {
    if (t[v].successors.empty()) {
        return std::make_pair(t, v);
    }
    double max = 0.0;
    int arg_max = t[v].successors.front();
    for (int w : t[v].successors) {
        if (t[w].selector.sims == 0) {
            return selection(t, w, c, r_l, r_t);
        }
        double s = t[w].selector.selectFunc(t[v].selector.sims, c, r_l, r_t);
        if (s > max) {
            max = s;
            arg_max = w;
        }
    }
    return selection(t, arg_max, c, r_l, r_t);
}

template <class State, class Domain, class Selector>
std::pair<Tree<State, Selector>, int> expansion(Tree<State, Selector> t,
                                                Domain domain,
                                                Selector selector,
                                                int v,
                                                int seed = 2021) {
    if (t[v].tasks.size() == 0 || t[v].selector.sims == 0) {
        return std::make_pair(t, v);
    }
    Task task = t[v].tasks.back();
    auto [task_id, args] = task;

    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(t[v].state, args);
        if (newstate) {
            Node<State, Selector> n;
            n.state = newstate.value();
            n.tasks = t[v].tasks;
            n.tasks.pop_back();
            n.depth = t[v].depth + 1;
            n.plan = t[v].plan;
            n.plan.second.push_back(task);
            n.selector = selector;
            n.pred = v;
            int w = boost::add_vertex(n, t);
            t[v].successors.push_back(w);
            return std::make_pair(t, w);
        }
        throw std::logic_error("Action Preconditions failed during expansion!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<int> c = {};
        for (auto method : relevant) {
            auto subtasks = method(t[v].state, args);
            if (subtasks.first) {
                Node<State, Selector> n;
                n.state = t[v].state;
                n.tasks = t[v].tasks;
                n.tasks.pop_back();
                n.depth = t[v].depth + 1;
                n.plan = t[v].plan;
                n.selector = selector;
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    n.tasks.push_back(*(--i));
                }
                n.pred = v;
                int w = boost::add_vertex(n, t);
                t[v].successors.push_back(w);
                c.push_back(w);
            }
        }
        int r = *select_randomly(c.begin(), c.end(), ++seed);
        return std::make_pair(t, r);
    }
    throw std::logic_error("No expansion possible!");
}

template <class State, class Domain, class Selector>
double simulation(
    State state, Tasks tasks, Domain domain, Selector sr, int seed = 2021) {
    if (tasks.size() == 0) {
        return sr.rewardFunc(state);
    }

    Task task = tasks.back();
    auto [task_id, args] = task;

    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(state, args);
        if (newstate) {
            tasks.pop_back();
            return simulation(newstate.value(), tasks, domain, sr, ++seed);
        }
        throw std::logic_error(
            "Action Preconditions failed during simulation!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<Tasks> options;
        for (auto method : relevant) {
            auto subtasks = method(state, args);
            if (subtasks.first) {
                Tasks temp = tasks;
                temp.pop_back();
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    temp.push_back(*(--i));
                }
                options.push_back(temp);
            }
        }
        Tasks r = *select_randomly(options.begin(), options.end(), ++seed);
        return simulation(state, r, domain, sr, ++seed);
    }
    throw std::logic_error("Simulation failed!");
}

template <class State, class Selector>
std::pair<Tree<State, Selector>, int> backprop(Tree<State, Selector> t, int w) {
    if (!(t[w].successors.empty())) {
        t[w].selector.mean = 0;
        t[w].selector.sims = t[w].selector.sims + 1;
        int total = t[w].successors.size();
        for (int c : t[w].successors) {
            t[w].selector.mean += t[c].selector.mean;
        }
        t[w].selector.mean /= total;
    }

    if (t[w].pred == -1) {
        return std::make_pair(t, w);
    }
    return backprop(t, t[w].pred);
}

template <class State, class Domain, class Selector>
Tree<State, Selector> seek_planMCTS(Tree<State, Selector> t,
                                    int v,
                                    Domain domain,
                                    Selector selector,
                                    double c,
                                    int r,
                                    int seed) {
    if (t[v].tasks.size() == 0) {
        t[boost::graph_bundle].plans.push_back(t[v].plan);
        std::cout << "Plan found at depth " << t[v].depth << std::endl;
        return t;
    }
    Tree<State, Selector> m;
    Node<State, Selector> n;
    n.state = t[v].state;
    n.tasks = t[v].tasks;
    n.depth = t[v].depth;
    n.plan = t[v].plan;
    n.selector = selector;
    int w = boost::add_vertex(n, m);
    std::pair<Tree<State, Selector>, int> mp(m, w);
    for (int i = 0; i < r; ++i) {
        mp = selection(mp.first, mp.second, c, r - i, r);
        mp = expansion(mp.first, domain, selector, mp.second, ++seed);
        State cState = mp.first[mp.second].state;
        Tasks cTasks = mp.first[mp.second].tasks;
        double results = simulation(cState, cTasks, domain, selector, ++seed);
        mp.first[mp.second].selector.mean = results;
        mp.first[mp.second].selector.sims =
            mp.first[mp.second].selector.sims + 1;
        mp = backprop(mp.first, mp.second);
    }
    if (mp.first[mp.second].successors.empty()) {
        throw std::logic_error("MCTS failed");
    }
    double max = 0.0;
    int arg_max = mp.first[mp.second].successors.front();
    for (int s : mp.first[mp.second].successors) {
        double mean = mp.first[s].selector.mean;
        if (mean > max) {
            max = mean;
            arg_max = s;
        }
    }
    Node<State, Selector> k;
    k.state = mp.first[arg_max].state;
    k.tasks = mp.first[arg_max].tasks;
    k.plan = mp.first[arg_max].plan;
    k.selector = selector;
    k.depth = t[v].depth + 1;
    k.pred = v;
    int y = boost::add_vertex(k, t);
    t[v].successors.push_back(y);
    return seek_planMCTS(t, y, domain, selector, c, r, ++seed);
}

template <class State, class Domain, class Selector>
bTasks cpphopMCTS(State state,
                  Tasks tasks,
                  Domain domain,
                  Selector selector,
                  double c,
                  int r,
                  int seed = 2021) {
    Tree<State, Selector> t;
    Node<State, Selector> root;
    root.state = state;
    root.tasks = tasks;
    root.plan = {};
    root.depth = 0;
    root.selector = selector;
    int v = boost::add_vertex(root, t);
    t = seek_planMCTS(t, v, domain, selector, c, r, seed);
    print(t[boost::graph_bundle].plans.back());
    return t[boost::graph_bundle].plans.back();
}
