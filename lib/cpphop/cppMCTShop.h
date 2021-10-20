#pragma once

#include "../util.h"
#include "typedefs.h"
#include "printing.h"
#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

template <class State>
struct pNode {
    State state;
    Tasks tasks;
    cTasks cplan;
    int depth;
    double mean = 0.0;
    int sims = 0;
    double likelihood;
    int pred = -1;
    std::vector<int> successors = {};
};

template <class State>
using pTree = std::vector<pNode<State>>;

template <class State>
int add_node(pNode<State>& n,pTree<State>& t) {
  t.push_back(n);
  return t.size() - 1;
}

template <class State>
int
cselection(pTree<State>& t,
          int v,
          double eps,
          int seed = 4021) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<> dis(0.0,1.0);
    while (!t[v].successors.empty()) {
      double e = dis(gen);
      if (e > eps) {
        std::vector<double> r_maxes = {};
        r_maxes.push_back(t[v].successors.front());
        double r_max = t[r_maxes.back()].mean;
        for (int w : t[v].successors) {
            if (t[w].sims == 0) {
              return w;
            }
            double s = t[w].mean;
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
        int v_max = t[v_maxes.back()].sims;
        for (int w : r_maxes) {
          int s = t[w].sims;
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
          if (t[w].sims == 0) {
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

template <class State>
void cbackprop(pTree<State>& t, int n, double r) {
  do {
    if (t[n].successors.empty()) {
      t[n].mean = r;
      t[n].sims++;
    }
    else {
      t[n].mean = (r + t[n].sims*t[n].mean)/(t[n].sims + 1);
      t[n].sims++;
    }
    n = t[n].pred;
  }
  while (n != -1);
  return;
}

template <class State, class Domain>
std::pair<int,double>
csimulation(State state,
           Tasks tasks,
           Domain& domain,
           CPM& cpm,
           double likelihood,
           double max_likelihood,
           double alpha,
           int seed) {
    while (!tasks.empty()) {
      Task task = tasks.back();

      if (in(task.task_id, domain.operators)) {
          Operator<State> op = domain.operators[task.task_id];
          std::optional<State> newstate = op(state, task.args);
          if (newstate) {
              pOperator<State> pop = domain.poperators[task.task_id];
              tasks.pop_back();
              likelihood = likelihood + log(pop(state,newstate.value(),task.args));
              if (likelihood < max_likelihood) {
                return std::make_pair(-1,likelihood);
              }
              seed++;
              state = newstate.value();
              continue;
          }
          return std::make_pair(-1,log(0.0));
      }

      if (in(task.task_id, domain.cmethods)) {
          auto relevant = domain.cmethods[task.task_id];
          std::vector<cTasks> c = {};
          std::string key = "";
          for (auto cmethod : relevant) {
              cTasks subtasks = cmethod(state, task.args);
              if (subtasks.first != "NIL") {
                c.push_back(subtasks);
                key += subtasks.first + "#";
              }
          }
          seed++;
          if (c.empty()) {
            return std::make_pair(-1,log(0.0));
          }
          cTasks r = *select_randomly(c.begin(), c.end(), seed);
          seed++;
          tasks.pop_back();
          if (r.first != "U") {
            if (cpm.find(key) != cpm.end()) {
              if (cpm[key].find(task.task_id) != cpm[key].end()) {
                if (cpm[key][task.task_id].find(r.first) != cpm[key][task.task_id].end()) {
                  likelihood = likelihood + log(cpm[key][task.task_id][r.first]); 
                }
                else {
                  likelihood = likelihood + log(alpha);
                }
              }
              else {
                likelihood = likelihood + log(alpha);
              }
            }
            else {
              likelihood = likelihood + log(alpha);
            }
          }
          else {
            likelihood = likelihood + log(1.0/c.size());
          }
          if (likelihood < max_likelihood) {
              return std::make_pair(-1,likelihood);
          }
          for (auto i = r.second.end();
              i != r.second.begin();) {
            tasks.push_back(*(--i));
          }
          continue;
      }
      std::string message = "Invalid task ";
      message += task.task_id;
      message += " during simulation!";
      throw std::logic_error(message);
    }
    if (likelihood < max_likelihood) {
      return std::make_pair(-1,likelihood);
    }
    if (likelihood == max_likelihood) {
      return std::make_pair(0,likelihood);
    }
    return std::make_pair(1,likelihood);
}

template <class State, class Domain>
int cexpansion(pTree<State>& t,
              int n,
              Domain& domain,
              CPM& cpm,
              double alpha,
              int seed = 4021) {
    Task task = t[n].tasks.back();

    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t[n].state, task.args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task.task_id];
            pNode<State> v;
            v.state = newstate.value();
            v.tasks = t[n].tasks;
            v.tasks.pop_back();
            v.depth = t[n].depth + 1;
            v.cplan = t[n].cplan;
            v.cplan.second.push_back(task);
            v.pred = n;
            v.likelihood = t[n].likelihood + log(pop(t[n].state,v.state,task.args));
            int w = add_node(v, t);
            t[n].successors.push_back(w);
            return w;
        }
        std::string message = task.task_id;
        message += " preconditions failed during expansion!";
        throw std::logic_error(
            message);
    }

    if (in(task.task_id, domain.cmethods)) {
        auto relevant = domain.cmethods[task.task_id];
        std::vector<cTasks> c = {};
        std::string key = "";
        for (auto cmethod : relevant) {
          cTasks subtasks = cmethod(t[n].state,task.args);
          if (subtasks.first != "NIL") {
            c.push_back(subtasks);
            key += subtasks.first + "#";
          }
        }
        
        std::vector<int> c_count = {};
        for (auto m : c) {
          pNode<State> v;
          if (r.first != "U") {
            if (cpm.find(key) != cpm.end()) {
              if (cpm[key].find(task.task_id) != cpm[key].end()) {
                if (cpm[key][task.task_id].find(r.first) != cpm[key][task.task_id].end()) {
                  v.likelihood = t[n].likelihood + log(cpm[key][task.task_id][r.first]); 
                }
                else {
                  v.likelihood = t[n].likelihood + log(alpha);
                }
              }
              else {
                v.likelihood = t[n].likelihood + log(alpha);
              }
            }
            else {
              v.likelihood = t[n].likelihood + log(alpha);
            }
          }
          else {
            v.likelihood = t[n].likelihood + log(1.0/c.size());
          }

          v.state = t[n].state;
          v.tasks = t[n].tasks;
          v.tasks.pop_back();
          v.depth = t[n].depth + 1;
          v.cplan = t[n].cplan;
          for (auto i = m.second.end();
              i != m.second.begin();) {
            v.tasks.push_back(*(--i));
          }
          v.pred = n;
          int w = add_node(v, t);
          t[n].successors.push_back(w);
          c_count.push_back(w);
        }
        //std::cout << total << std::endl;
        seed++;
        if (c_count.empty()) {   
          return n;
        }
        int r = *select_randomly(c_count.begin(), c_count.end(), seed);
        return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain>
cTasks
cseek_planMCTS(pTree<State>& t,
                 int v,
                 Domain& domain,
                 CPM& cpm,
                 int R = 30,
                 double eps = 0.4,
                 double alpha = 0.5,
                 int seed = 4021,
                 int aux_R = 10) {

  double max_likelihood = log(0.0);
  while (!t[v].tasks.empty()) {
    pTree<State> m;
    pNode<State> n_node;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.cplan = t[v].cplan;
    n_node.likelihood = t[v].likelihood;
    int w = add_node(n_node, m);
    int aux = aux_R;
    for (int i = 0; i < R; i++) {
      int n = cselection(m,w,eps,seed);
      seed++;
      if (m[n].tasks.empty()) {
          auto r = csimulation(m[n].state, m[n].tasks, domain, cpm, m[n].likelihood,max_likelihood,alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          cbackprop(m,n,r.first);
      }
      else {
        if (m[n].sims == 0) {
          auto r = csimulation(m[n].state, m[n].tasks, domain, cpm, m[n].likelihood,max_likelihood,alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          cbackprop(m,n,r.first);
        }
        else {
          int n_p = cexpansion(m,n,domain,cpm,alpha,seed);
          if (n_p == n) {
            if (aux == 0) {
              throw std::logic_error("Out of auxiliary resources, shutting down!");   
            }
            aux--;
            i--;
          }
          else {
            aux = aux_R;
          }
          seed++;
          auto r = csimulation(m[n_p].state, m[n_p].tasks, domain, cpm, m[n_p].likelihood,max_likelihood,alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          cbackprop(m,n_p,r.first);
        }
      }
    }
    int arg_max = m[w].successors.front();
    double max = m[arg_max].mean;
    for (int s : m[w].successors) {
        double mean = m[s].mean;
        if (mean > max) {
            max = mean;
            arg_max = s;
        }
    }
    pNode<State> k;
    k.state = m[arg_max].state;
    k.tasks = m[arg_max].tasks;
    k.cplan = m[arg_max].cplan;
    k.depth = t[v].depth + 1;
    k.pred = v;
    k.likelihood = m[arg_max].likelihood;
    int y = add_node(k, t);
    t[v].successors.push_back(y);
    seed++;
    v = y;
  }
  std::cout << "Plan found at depth " << t[v].depth;
  std::cout << " with likelihood " << t[v].likelihood << std::endl;
  std::cout << std::endl;
  std::cout << "Final State:" << std::endl;
  std::cout << t[v].state.to_json() << std::endl;
  std::cout << std::endl;
  return t[v].cplan;

}

template <class State, class Domain>
std::pair<pTree<State>,int> cppMCTShop(State state,
                  Tasks tasks,
                  Domain& domain,
                  CPM& cpm,
                  int R,
                  double eps = 0.4,
                  double alpha = 0.5,
                  int seed = 4021,
                  int aux_R = 10) {
    pTree<State> t;
    pNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.cplan = {};
    root.depth = 0;
    root.likelihood = 0.0;
    int v = add_node(root, t);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    std::cout << t[v].state.to_json() << std::endl;
    std::cout << std::endl;
    auto plan = cseek_planMCTS(t, v, domain, cpm, R, eps, alpha, seed);
    std::cout << "Plan:" << std::endl;
    print(plan);
    return std::make_pair(t,v);
}
