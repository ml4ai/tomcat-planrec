#pragma once

#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include "Node.hpp"
#include "Tree.hpp"
#include "util.h"

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
template <class Element>
bool in(Element element, std::vector<Element> v) {
    return std::count(v.begin(),v.end(), element);
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
  for (auto bt : plans ) {
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
            bTasks solution = seek_plan(
                newstate.value(), tasks, plan, domain, depth + 1);
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

template <class State, class Domain, class Selector>
Tree<State,Selector> seek_planDFS(Tree<State, Selector> t,
                 int v,
                 Domain domain) {
    std::cout << "depth: " << t[v].depth << std::endl;
    std::cout << "tasks: ";
    print(t[v].tasks);
    std::cout << std::endl;
    if (t[v].tasks.size() == 0) {
        t[boost::graph_bundle].plans.push_back(t[v].plan);
        std::cout << "Plan found at depth " << t[v].depth << std::endl;
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
            int w = boost::add_vertex(n,t);
            return seek_planDFS(t,w,domain);
        }
        std::cout << "Action Preconditions Failed at depth " << t[v].depth << ", BackTracking!" << std::endl;
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
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    n.tasks.push_back(*(--i));
                }
                int w = boost::add_vertex(n,t);
                t = seek_planDFS(t,w,domain);
            }
        }
        return t;
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

template <class State, class Domain, class Selector>
Plans cpphopDFS(State state,
             Tasks tasks,
             Domain domain,
             Selector selector) {
    Tree<State,Selector> t;
    Node<State,Selector> root;
    root.state = state;
    root.tasks = tasks;
    root.plan = {};
    root.depth = 0;
    int v = boost::add_vertex(root,t);
    t = seek_planDFS(t,v,domain);
    print(t[boost::graph_bundle].plans);
    return t[boost::graph_bundle].plans;
}

template <class State, class Selector>
std::pair<Tree<State, Selector>,int> selection(Tree<State,Selector> t, int v, double c, int r_l, int r_t) {
  std::vector<int> successors = get_successor_list(t,v);
  if (successors.empty()) {
    return std::make_pair(t,v);
  }
  double max = 0.0;
  int arg_max = successors.front();
  for (int w : successors) {
    if (t[w].selector.sims == 0) {
      return selection(t,w,c,r_l,r_t);
    }
    double s = t[w].selector.selectFunc(t[v].selector.mean,c,r_l,r_t);
    if (s > max) {
      max = s;
      arg_max = w;
    }
  }
  return selection(t,arg_max,c,r_l,r_t);
}

template <class State, class Domain, class Selector>
std::pair<Tree<State, Selector>, int> expansion(Tree<State,Selector> t, Domain domain, int v, int seed = 2021) {
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
            int w = boost::add_vertex(n,t);
            return std::make_pair(t,w);
        }
        throw std::logic_error("Action Preconditions failed during expansion!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<int> c;
        for (auto method : relevant) {
            auto subtasks = method(t[v].state, args);
            if (subtasks.first) {
                Node<State, Selector> n;
                n.state = t[v].state;
                n.tasks = t[v].tasks;
                n.tasks.pop_back();
                n.depth = t[v].depth + 1;
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    n.tasks.push_back(*(--i));
                }
                int w = boost::add_vertex(n,t);
                c.push_back(w);
            }
        }
        int r = *select_randomly(c.begin(),c.end(),seed);
        return std::make_pair(t,r);
    }
    throw std::logic_error("No expansion possible!");
 
}

template <class State, class Domain, class Selector>
double simulation(State state, Tasks tasks, Domain domain, Selector sr, int seed = 2021) {
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
          return simulation(newstate,tasks,domain,sr,seed);
      }
      throw std::logic_error("Action Preconditions failed during simulation!");
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
      Tasks r = *select_randomly(options.begin(),options.end(), seed);
      return simulation(state,r,domain,sr,seed); 
  }
  throw std::logic_error("Simulation failed!");


}

template <class State, class Selector>
std::pair<Tree<State, Selector>,int> backprop(Tree<State, Selector> t, int w) {
  std::vector<int> successors = get_successor_list(t,w);
  if (!(successors.empty())) {
    t[w].selector.mean = 0;
    t[w].selector.sims = t[w].selector.sims + 1;
    for (int c : successors) {
      t[w].selector.mean += t[c].selector.mean;
    }
    t[w].selector.mean /= successors.size();
  }

  std::vector<int> predecessors = get_predecessor_list(t,w);
  if (predecessors.empty()) {
    return std::make_pair(t,w);
  }

  return backprop(t,predecessors.back());
    
}
