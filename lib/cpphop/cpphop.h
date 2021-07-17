#pragma once

#include "../util.h"
#include "Node.h"
#include "Tree.h"
#include "printing.h"
#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

template <class State, class Domain>
pTasks seek_plan(State state,
                 std::vector<Task> tasks,
                 pTasks plan,
                 Domain domain,
                 int depth) {
    std::cout << "depth: " << depth << std::endl;
    std::cout << "tasks: ";
    print(tasks);
    std::cout << std::endl;
    if (tasks.size() == 0) {
        return pTasks(1, plan.second);
    }

    Task task = tasks.back();
    auto [task_id, args] = task;
    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(state, args);
        if (newstate) {
            tasks.pop_back();
            plan.second.push_back(task);
            pTasks solution =
                seek_plan(newstate.value(), tasks, plan, domain, depth + 1);
            if (solution.first) {
                return solution;
            }
        }
        return {0, {}};
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
                pTasks solution =
                    seek_plan(state, tasks, plan, domain, depth + 1);
                if (solution.first) {
                    return solution;
                }
            }
        }
        return {0, {}};
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
pTasks cpphop(State state, Tasks tasks, Domain domain) {
    pTasks result = seek_plan(state, tasks, {}, domain, 0);
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
int
selection(Tree<State, Selector> t, 
          int v, 
          double eps, 
          int seed = 4021) {
    if (t[v].successors.empty()) {
        return v;
    }
    seed++;
    std::mt19937 gen(seed);
    seed++;
    std::uniform_real_distribution<> dis(0.0,1.0);
    double e = dis(gen);
    if (e > eps) {
      std::vector<double> r_maxes = {};
      r_maxes.push_back(t[v].successors.front());
      double r_max = t[r_maxes.back()].selector.mean;
      for (int w : t[v].successors) {
          if (t[w].selector.sims == 0) {
            return w;
          }
          double s = t[w].selector.mean;
          if (s >= r_max) {
            if (s > r_max) {
              r_max = s;
              r_maxes.clear();
              r_maxes.push_back(w);
            }
            else {
              r_maxes.push_back(w);
            }
          }
      }
      std::vector<double> v_maxes = {};
      v_maxes.push_back(r_maxes.front());
      int v_max = t[v_maxes.back()].selector.sims;
      for (int w : r_maxes) {
        int s = t[w].selector.sims;
        if (s >= v_max) {
          if (s > v_max) {
            v_max = s;
            v_maxes.clear();
            v_maxes.push_back(w);
          }
          else {
            v_maxes.push_back(w);
          }
        }
      }
      seed++;
      int n = *select_randomly(v_maxes.begin(), v_maxes.end(), seed);
      seed++;
      return selection(t, n, eps, seed);
    }
    else {
      for (int w : t[v].successors) {
        if (t[w].selector.sims == 0) {
          return w;
        }
      }
      seed++;
      int n = *select_randomly(t[v].successors.begin(), t[v].successors.end(), seed);
      seed++;
      return selection(t,n,eps,seed);
    }
}

template <class State, class Selector>
Tree<State, Selector> backprop(Tree<State, Selector> t, int n, double r) {
  if (t[n].successors.empty()) {
    t[n].selector.mean = r;
    t[n].selector.sims++;
  }
  else {
    t[n].selector.mean = (r + t[n].selector.sims*t[n].selector.mean)/(t[n].selector.sims + 1);
    t[n].selector.sims++;
  }
  if (t[n].pred == -1) {
    return t;
  }

  return backprop(t,t[n].pred,r);
}

template <class State, class Domain, class Selector>
double
simulation(Tree<State, Selector> t, 
           int n, 
           Domain domain,
           Selector selector,
           int seed) {
    std::cout << seed << std::endl;
    if (t[n].tasks.empty()) {
        return t[n].likelihood;
    }

    Task task = t[n].tasks.back();
    auto [task_id, args] = task;
    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(t[n].state, args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task_id];
            Node<State, Selector> v;
            v.state = newstate.value();
            v.tasks = t[n].tasks;
            v.tasks.pop_back();
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.plan.second.push_back(task);
            v.selector = selector;
            v.pred = n;
            v.likelihood = t[n].likelihood*pop(t[n].state,v.state,args);
            int w = boost::add_vertex(v, t);
            t[n].successors.push_back(w);
            seed++;
            return simulation(t, w, domain, selector,seed);
        }
        std::cout << task_id << std::endl;
        throw std::logic_error(
            "Action Preconditions failed during simulation!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<int> c = {};
        std::vector<double> wts = {};
        for (auto method : relevant) {
            pTasks subtasks = method(t[n].state, args);
            if (subtasks.first) {
                wts.push_back(subtasks.first);
                Node<State, Selector> v;
                v.state = t[n].state;
                v.tasks = t[n].tasks;
                v.tasks.pop_back();
                v.depth = t[n].depth + 1;
                v.plan = t[n].plan;
                v.selector = selector;
                v.likelihood = t[n].likelihood*subtasks.first;
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    v.tasks.push_back(*(--i));
                }
                v.pred = n;
                int w = boost::add_vertex(v, t);
                t[n].successors.push_back(w);
                c.push_back(w);
            }
        }
        seed++;
        int r = sample_method(c,wts,seed);
        seed++;
        return simulation(t,r,domain,selector,seed);
    }
    throw std::logic_error("Invalid task during simulation!");
}

template <class State, class Domain, class Selector>
std::pair<Tree<State, Selector>, int> expansion(Tree<State, Selector> t,
                                                int n,
                                                Domain domain,
                                                Selector selector,
                                                int seed = 4021) {
    Task task = t[n].tasks.back();
    auto [task_id, args] = task;

    if (in(task_id, domain.operators)) {
        Operator<State> op = domain.operators[task_id];
        std::optional<State> newstate = op(t[n].state, args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task_id];
            Node<State, Selector> v;
            v.state = newstate.value();
            v.tasks = t[n].tasks;
            v.tasks.pop_back();
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.plan.second.push_back(task);
            v.selector = selector;
            v.pred = n;
            v.likelihood = t[n].likelihood*pop(t[n].state,v.state,args); 
            int w = boost::add_vertex(v, t);
            t[n].successors.push_back(w);
            return std::make_pair(t, w);
        }
        throw std::logic_error("Action Preconditions failed during expansion!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<int> c = {};
        //double total;
        for (auto method : relevant) {
            pTasks subtasks = method(t[n].state, args);
            if (subtasks.first) {
                //total += subtasks.first;
                Node<State, Selector> v;
                v.state = t[n].state;
                v.tasks = t[n].tasks;
                v.tasks.pop_back();
                v.depth = t[n].depth + 1;
                v.plan = t[n].plan;
                v.selector = selector;
                v.likelihood = t[n].likelihood*subtasks.first;
                for (auto i = subtasks.second.end();
                     i != subtasks.second.begin();) {
                    v.tasks.push_back(*(--i));
                }
                v.pred = n;
                int w = boost::add_vertex(v, t);
                t[n].successors.push_back(w);
                c.push_back(w);
            }
        }
        //std::cout << total << std::endl;
        seed++;
        int r = *select_randomly(c.begin(), c.end(), seed);
        return std::make_pair(t, r);
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain, class Selector>
Tree<State,Selector>
seek_planMCTS(Tree<State,Selector> t,
                 int v,
                 Domain domain, 
                 Selector selector,
                 int N = 30,
                 double eps = 0.4,
                 int seed = 4021) {
  if (t[v].tasks.empty()) {
        t[boost::graph_bundle].plans.push_back(t[v].plan);
        std::cout << "Plan found at depth " << t[v].depth << " and score of " << t[v].selector.rewardFunc(t[v].state);
        std::cout << " with likelihood " << t[v].likelihood << std::endl;
        std::cout << std::endl;
        std::cout << "Final State:" << std::endl;
        std::cout << t[v].state.to_json() << std::endl;
        std::cout << std::endl;
        return t;
  }
  Tree<State, Selector> m;
  Node<State, Selector> n;
  n.state = t[v].state;
  n.tasks = t[v].tasks;
  n.depth = t[v].depth;
  n.plan = t[v].plan;
  n.selector = selector;
  n.likelihood = t[v].likelihood;
  int w = boost::add_vertex(n, m);
  for (int i = 0; i < N; i++) {
    int n = selection(m,w,eps,seed);
    seed++;
    if (m[n].tasks.empty()) {
        double r = simulation(m, n, domain, selector,seed);
        m = backprop(m,n,r);
    }
    else {
      if (m[n].selector.sims == 0) {
        double r = simulation(m, n, domain, selector,seed);
        seed++;
        m = backprop(m,n,r);
      }
      else {
        auto [m_new, n_p] = expansion(m,n,domain,selector,seed);
        seed++;
        double r = simulation(m_new, n_p, domain, selector,seed);
        seed++;
        m = backprop(m_new,n_p,r);   
      }
    }
  } 
  int arg_max = m[w].successors.front();
  double max = m[arg_max].selector.mean;
  for (int s : m[w].successors) {
      double mean = m[s].selector.mean;
      if (mean > max) {
          max = mean;
          arg_max = s;
      }
  }
  Node<State, Selector> k;
  k.state = m[arg_max].state;
  k.tasks = m[arg_max].tasks;
  k.plan = m[arg_max].plan;
  k.selector = selector;
  k.depth = t[v].depth + 1;
  k.pred = v;
  k.likelihood = m[arg_max].likelihood;
  int y = boost::add_vertex(k, t);
  t[v].successors.push_back(y);
  seed++;
  return seek_planMCTS(t, y, domain, selector, N, eps, seed);
}

template <class State, class Domain, class Selector>
std::pair<Tree<State,Selector>,int> cpphopMCTS(State state,
                  Tasks tasks,
                  Domain domain,
                  Selector selector,
                  int N,
                  double eps = 0.4,
                  int seed = 4021) {
    Tree<State, Selector> t;
    Node<State, Selector> root;
    root.state = state;
    root.tasks = tasks;
    root.plan = {};
    root.depth = 0;
    root.selector = selector;
    root.likelihood = 1;
    int v = boost::add_vertex(root, t);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    std::cout << t[v].state.to_json() << std::endl;
    std::cout << std::endl;
    t = seek_planMCTS(t, v, domain, selector, N, eps, seed);
    std::cout << "Plan:" << std::endl;
    print(t[boost::graph_bundle].plans.back());
    return std::make_pair(t,v);
}
