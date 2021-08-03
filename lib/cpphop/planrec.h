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
#include "../util.h"
#include <nlohmann/json.hpp>
#include <math.h>
#include <random>
#include <cfloat>

using json = nlohmann::json;

template <class State, class Selector>
int
selection_rec(Tree<State, Selector>& t,
          int v,
          double eps,
          int seed = 2021) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<> dis(0.0,1.0);
    while (!t[v].successors.empty()) {
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
        v = *select_randomly(v_maxes.begin(), v_maxes.end(), seed);
        seed++;
      }
      else {
        for (int w : t[v].successors) {
          if (t[w].selector.sims == 0) {
            return w;
          }
        }
        seed++;
        v = *select_randomly(t[v].successors.begin(), t[v].successors.end(), seed);
        seed++;
      }
    }
    return v;
}

template <class State, class Selector>
void backprop_rec(Tree<State, Selector>& t, int n, double r) {
  do {
    if (t[n].successors.empty()) {
      t[n].selector.mean = r;
      t[n].selector.sims++;
    }
    else {
      t[n].selector.mean = (r + t[n].selector.sims*t[n].selector.mean)/(t[n].selector.sims + 1);
      t[n].selector.sims++;
    }
    n = t[n].pred;
  }
  while (n != -1);
  return;
}

template <class State, class Domain>
double
simulation_rec(json& trace,
           json plan_trace,
           State state,
           Tasks tasks,
           Domain& domain,
           double likelihood,
           int seed) {

    while (plan_trace.size() < trace.size()) {
      Task task = tasks.back();

      if (in(task.task_id, domain.operators)) {
          Operator<State> op = domain.operators[task.task_id];
          std::optional<State> newstate = op(state, task.args);
          if (newstate) {
              pOperator<State> pop = domain.poperators[task.task_id];
              tasks.pop_back();
              likelihood = likelihood*pop(state,newstate.value(),task.args);
              json g;
              g["task"] = task2string(task);
              g["pre-state"] = state.to_json();
              state = newstate.value();
              g["post-state"] = state.to_json();
              plan_trace.push_back(g);
              seed++;
              continue;
          }
          std::string message = task.task_id;
          message += " preconditions failed during simulation!";
          throw std::logic_error(
              message);
      }

      if (in(task.task_id, domain.methods)) {
          auto relevant = domain.methods[task.task_id];
          std::vector<pTasks> c = {};
          for (auto method : relevant) {
              pTasks subtasks = method(state, task.args);
              if (subtasks.first) {
                c.push_back(subtasks);
              }
          }
          seed++;
          if (c.empty()) {
            std::string message = "No valid method for ";
            message += task.task_id;
            message += " during simulation!";
            throw std::logic_error(message);
          }
          pTasks r = *select_randomly(c.begin(), c.end(), seed);
          seed++;
          tasks.pop_back();
          likelihood = likelihood*r.first;
          for (auto i = r.second.end();
              i != r.second.begin();) {
            tasks.push_back(*(--i));
          }
          continue;
      }   
      std::string message = "No valid method for ";
      message += task.task_id;
      message += " during simulation!";
      throw std::logic_error(message);
    }
    if (plan_trace == trace) {
      return likelihood;
    }
    return 0;
}

template <class State, class Domain, class Selector>
int expansion_rec(Tree<State, Selector>& t,
                  int n,
                  Domain& domain,
                  Selector selector,
                  int seed = 2021) {
    Task task = t[n].tasks.back();

    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t[n].state, task.args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task.task_id];
            Node<State, Selector> v;
            v.state = newstate.value();
            v.tasks = t[n].tasks;
            v.tasks.pop_back();
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.plan.second.push_back(task);
            v.selector = selector;
            v.pred = n;
            v.likelihood = t[n].likelihood*pop(t[n].state,v.state,task.args); 
            v.plan_trace = t[n].plan_trace;
            json g;
            g["task"] = task2string(task);
            g["pre-state"] = t[n].state.to_json();
            g["post-state"] = v.state.to_json();
            v.plan_trace.push_back(g);
            int w = boost::add_vertex(v, t);
            t[n].successors.push_back(w);
            return w;
        }
        throw std::logic_error("Action Preconditions failed during expansion!");
    }

    if (in(task.task_id, domain.methods)) {
        auto relevant = domain.methods[task.task_id];
        std::vector<int> c = {};
        for (auto method : relevant) {
            pTasks subtasks = method(t[n].state, task.args);
            if (subtasks.first) {
                Node<State, Selector> v;
                v.state = t[n].state;
                v.tasks = t[n].tasks;
                v.tasks.pop_back();
                v.depth = t[n].depth + 1;
                v.plan = t[n].plan;
                v.selector = selector;
                v.likelihood = t[n].likelihood*subtasks.first;
                v.plan_trace = t[n].plan_trace;
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
        return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain, class Selector>
void
seek_planrecMCTS(json& trace,
                 Tree<State,Selector>& t,
                 int v,
                 Domain& domain,
                 Selector selector,
                 int N = 30,
                 double eps = 0.4,
                 int seed = 2021) {
  while (t[v].plan_trace.size() < trace.size()) {
    Tree<State, Selector> m;
    Node<State, Selector> n_node;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    n_node.plan_trace = t[v].plan_trace;
    n_node.selector = selector;
    n_node.likelihood = t[v].likelihood;
    int w = boost::add_vertex(n_node, m);
    for (int i = 0; i < N; i++) {
      int n = selection_rec(m,w,eps,seed);
      seed++;
      if (m[n].plan_trace.size() >= trace.size()) {
        if (m[n].plan_trace == trace) {
          backprop_rec(m,n,m[n].likelihood);
        }
        backprop_rec(m,n,0);
      }
      else {
        if (m[n].selector.sims == 0) {
          double r = simulation_rec(trace,m[n].plan_trace,m[n].state, m[n].tasks, domain, m[n].likelihood,seed);
          seed++;
          backprop_rec(m,n,r);
        }
        else {
          int n_p = expansion_rec(m,n,domain,selector,seed);
          seed++;
          double r = simulation_rec(trace,m[n_p].plan_trace,m[n_p].state, m[n_p].tasks, domain, m[n_p].likelihood,seed);
          seed++;
          backprop_rec(m,n_p,r);   
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
    k.plan_trace = m[arg_max].plan_trace;
    k.selector = selector;
    k.depth = t[v].depth + 1;
    k.pred = v;
    k.likelihood = m[arg_max].likelihood;
    int y = boost::add_vertex(k, t);
    t[v].successors.push_back(y);
    seed++;
    v = y;
  }
  return;
 
}

template <class State, class Domain, class Selector>
std::pair<Tree<State,Selector>,int> 
cpphopPlanrecMCTS(json& trace,
                  State state,
                  Tasks tasks,
                  Domain& domain,
                  Selector selector,
                  int N = 30,
                  double eps = 0.4,
                  int seed = 2021) {
    Tree<State, Selector> t;
    Node<State, Selector> root;
    root.state = state;
    root.tasks = tasks;
    root.plan = {};
    root.depth = 0;
    root.selector = selector;
    root.likelihood = 1;
    int v = boost::add_vertex(root, t);
    seek_planrecMCTS(trace,t, v, domain, selector, N, eps, seed);
    return std::make_pair(t,v);
}
