#pragma once

#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include "Node.h"
#include "Tree.h"
#include "util.h"
#include <nlohmann/json.hpp>
#include <math.h>
#include <random>

using json = nlohmann::ordered_json;

template <class State, class Selector>
int
selection(Tree<State, Selector> t, 
          int v, 
          double eps, 
          int seed = 2021) {
    if (t[v].successors.empty()) {
        return v;
    }
    std::mt19937 gen(seed);
    seed++;
    std::uniform_real_distribution<> dis(0.0,1.0);
    double e = dis(gen);
    if (e > eps) {
      std::vector<double> r_maxes = {};
      r_maxes.push_back(t[v].successors.front());
      double max = t[r_maxes.back()].selector.mean;
      for (int w : t[v].successors) {
          if (t[w].selector.sims == 0) {
            return w;
          }
          double s = t[w].selector.mean;
          if (s >= max) {
            if (s > max) {
              max = s;
              r_maxes.clear();
              r_maxes.push_back(w);
            }
            else {
              r_maxes.push_back(w);
            }
          }
      }
      std::vector<double> v_maxes = {}
      v_maxes.push_back(r_maxes.front());
      int max = t[v_maxes.back()].selector.sims;
      for (int w : r_maxes) {
        int s = t[w].selector.sims;
        if (s >= max) {
          if (s > max) {
            max = s;
            v_maxes.clear();
            v_maxes.push_back(w);
          }
          else {
            v_maxes.push_back(w);
          }
        }
      }
      int n = *select_randomly(v_maxes.begin(), v_maxes.end(), ++seed);
      seed++;
      return selection(t, n, eps, seed);
    }
    else {
      for (int w : t[v].successors) {
        if (t[w].selector.sims == 0) {
          return w;
        }
      }
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
    t[n].selector.mean = 0;
    t[n].selector.sims++;
    int total = t[n].successors.size();
    for (int w : t[n].successors) {
      t[n].selector.mean += t[w].selector.mean;
    }
    t[n].selector.mean /= total;
  }

  if (t[n].pred == -1) {
    return t;
  }
  return backprop(t,t[n].pred,r);
}

template <class State, class Domain, class Selector>
double
simulation(json trace, 
           Tree<State, Selector> t, 
           int n, 
           Domain domain,
           Selector selector,
           int seed) {
    if (t[n].plan_trace.size() >= trace.size()) {
      if (t[n].plan_trace == trace) {
        return t[n].log_likelihood;
      }
      return 0;
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
            v.log_likelihood = t[n].log_likelihood + log(pop(t[n].state,v.state,args));
            json g;
            g["task"] = task2string(task);
            g["pre-state"] = t[n].state.to_json();
            g["post-state"] = v.state.to_json();
            v.plan_trace.push_back(g);
            int w = boost::add_vertex(v, t);
            t[n].successors.push_back(w);
            return simulation(trace, t, w, domain, selector,seed);
        }
        throw std::logic_error(
            "Action Preconditions failed during simulation!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<int> c = {};
        for (auto method : relevant) {
            pTasks subtasks = method(t[n].state, args);
            if (subtasks.first) {
                Node<State, Selector> v;
                v.state = t[n].state;
                v.tasks = t[n].tasks;
                v.tasks.pop_back();
                v.depth = t[n].depth + 1;
                v.plan = t[n].plan;
                v.selector = selector;
                v.log_likelihood = t[n].log_likelihood + log(subtasks.first);
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
        int r = *select_randomly(c.begin(), c.end(), seed);
        seed++;
        return simulation(trace,t,r,domain,selector,seed);
    }
    throw std::logic_error("Invalid task during simulation!");
}

template <class State, class Domain, class Selector>
std::pair<Tree<State, Selector>, int> expansion(Tree<State, Selector> t,
                                                int n,
                                                Domain domain,
                                                Selector selector,
                                                int seed = 2021) {
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
            v.log_likelihood = t[n].log_likelihood + log(pop(t[n].state,v.state,args)); 
            json g;
            g["task"] = task2string(task);
            g["pre-state"] = t[n].state.to_json();
            g["post-state"] = v.state.to_json();
            v.plan_trace.push_back(g);
            int w = boost::add_vertex(v, t);
            t[n].successors.push_back(w);
            return std::make_pair(t, w);
        }
        throw std::logic_error("Action Preconditions failed during expansion!");
    }

    if (in(task_id, domain.methods)) {
        auto relevant = domain.methods[task_id];
        std::vector<int> c = {};
        for (auto method : relevant) {
            pTasks subtasks = method(t[n].state, args);
            if (subtasks.first) {
                Node<State, Selector> v;
                v.state = t[n].state;
                v.tasks = t[n].tasks;
                v.tasks.pop_back();
                v.depth = t[n].depth + 1;
                v.plan = t[n].plan;
                v.selector = selector;
                v.log_likelihood = t[n].log_likelihood + log(subtasks.first);
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
        int r = *select_randomly(c.begin(), c.end(), ++seed);
        return std::make_pair(t, r);
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain, class Selector>
Tree<State, Selector>
get_optimal_branch(Tree<State, Selector> t, Tree<State,Selector> o, int t_n, int o_n) {
  if (t[t_n].successors.empty()) {
    return o;
  }
  int arg_max = t[t_n].successors.front();
  double max = t[arg_max].selector.mean;
  for (int v : t[t_n].successors) {
    double s = t[v].selector.mean;
    if (s > max) {
      max = s;
      arg_max = v;
    }
  }
  Node<State, Selector> v;
  v.state = t[arg_max].state;
  v.tasks = t[arg_max].tasks;
  v.depth = t[arg_max].depth + 1;
  v.plan = t[arg_max].plan;
  v.selector = t[arg_max].selector;
  v.pred = t[arg_max].pred;
  v.log_likelihood = t[arg_max].log_likelihood; 
  v.plan_trace = t[arg_max].plan_trace;
  int w = boost::add_vertex(v, o);
  o[o_n].successors.push_back(w);

  return get_optimal_branch(t,o,arg_max,w);
 
}

template <class State, class Domain, class Selector>
json
seek_planrecMCTS(json trace,
                 State state,
                 Tasks tasks,
                 Domain domain, 
                 Selector selector,
                 int N = 30,
                 double eps = 0.4,
                 int seed = 2021,
                 bool gen_file = false,
                 std::string outfile = "plan_explanation.json") {
  Tree<State, Selector> t;
  Node<State, Selector> root;
  root.state = state;
  root.tasks = tasks;
  root.plan = {};
  root.depth = 0;
  root.log_likelihood = 0;
  root.selector = selector;
  int v = boost::add_vertex(root, t);
  for (int i = 0; i < N; i++) {
    int n = selection(t,v,eps,seed);
    seed++;
    if (t[n].plan_trace.size() >= trace.size()) {
      if (t[n].plan_trace == trace) {
        t = backprop(t,n,t[n].log_likelihood);
      }
      t = backprop(t,n,0);
    }
    else {
      if (t[n].selector.sims == 0) {
        double r = simulation(trace, t, n, domain, selector,seed);
        seed++;
        t = backprop(t,n,r);
      }
      else {
        auto [t, n_p] = expansion(t,n,domain,selector,seed);
        seed++;
        double r = simulation(trace, t, n_p, domain, selector,seed);
        seed++;
        t = backprop(t,n_p,r);   
      }
    }
  } 
  Tree<State, Selector> o;
  int o_n = boost::add_vertex(root,o);
  o = get_optimal_branch(t,o,v,o_n);
  return generate_plan_trace_tree(o,o_n, gen_file, outfile);
}
