#pragma once

#include "../util.h"
#include "cpphop.h"
#include "typedefs.h"
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

// MCTS algorithms
// See Tree.hpp for why boost::edges are not used and why
// the successor/predecessor functions are not used
template <class State, class Selector>
int
cselection(Tree<State, Selector>& t,
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
void cbackprop(Tree<State, Selector>& t, int n, double r) {
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
std::pair<int,double>
csimulation(State state,
           Tasks tasks,
           Domain& domain,
           CFM& cfm,
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
          double f_total = 0;
          bool no_task = false;
          for (auto cmethod : relevant) {
              cTasks subtasks = cmethod(state, task.args);
              if (subtasks.first != "NIL") {
                c.push_back(subtasks);
                if (cfm.find(task.task_id) != cfm.end()) {
                  if(cfm[task.task_id].find(subtasks.first) != cfm[task.task_id].end()) {
                    f_total += cfm[task.task_id][subtasks.first];
                  }
                  else {
                    f_total += alpha;
                  }
                }
                else {
                  no_task = true;
                  f_total += alpha;
                }
              }
          }
          seed++;
          if (c.empty()) {
            return std::make_pair(-1,log(0.0));
          }
          cTasks r = *select_randomly(c.begin(), c.end(), seed);
          seed++;
          tasks.pop_back();
          if (!no_task) {
            if(cfm[task.task_id].find(r.first) != cfm[task.task_id].end()) {
              likelihood = likelihood + log((cfm[task.task_id][r.first]/f_total));
            }
            else {
              likelihood = likelihood + log((alpha/f_total));
            }
          }
          else {
            likelihood = likelihood + log((alpha/f_total));
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

template <class State, class Domain, class Selector>
int cexpansion(Tree<State, Selector>& t,
              int n,
              Domain& domain,
              CFM& cfm,
              Selector selector,
              double alpha,
              int seed = 4021) {
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
            v.cplan = t[n].cplan;
            v.cplan.second.push_back(task);
            v.selector = selector;
            v.pred = n;
            v.likelihood = t[n].likelihood + log(pop(t[n].state,v.state,task.args));
            int w = boost::add_vertex(v, t);
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
        double f_total = 0;
        bool no_task = false;
        for (auto cmethod : relevant) {
          cTasks subtasks = cmethod(t[n].state,task.args);
          if (subtasks.first != "NIL") {
            c.push_back(subtasks);
            if (cfm.find(task.task_id) != cfm.end()) {
              if(cfm[task.task_id].find(subtasks.first) != cfm[task.task_id].end()) {
                f_total += cfm[task.task_id][subtasks.first];
              }
              else {
                f_total += alpha;
              }
            }
            else {
              no_task = true;
              f_total += alpha;
            }
          }
        }
        
        std::vector<int> c_count = {};
        for (auto m : c) {
          Node<State, Selector> v;
          if (!no_task) {
            if(cfm[task.task_id].find(m.first) != cfm[task.task_id].end()) {
              v.likelihood = t[n].likelihood + log((cfm[task.task_id][m.first]/f_total));
            }
            else {
              v.likelihood = t[n].likelihood + log((alpha/f_total));
            }
          }
          else {
            v.likelihood = t[n].likelihood + log((alpha/f_total));
          }
          v.state = t[n].state;
          v.tasks = t[n].tasks;
          v.tasks.pop_back();
          v.depth = t[n].depth + 1;
          v.cplan = t[n].cplan;
          v.selector = selector;
          for (auto i = m.second.end();
              i != m.second.begin();) {
            v.tasks.push_back(*(--i));
          }
          v.pred = n;
          int w = boost::add_vertex(v, t);
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

template <class State, class Domain, class Selector>
void
cseek_planMCTS(Tree<State,Selector>& t,
                 int v,
                 Domain& domain,
                 CFM& cfm,
                 Selector selector,
                 int R = 30,
                 double eps = 0.4,
                 double alpha = 0.5,
                 int seed = 4021) {

  double max_likelihood = log(0.0);
  while (!t[v].tasks.empty()) {
    Tree<State, Selector> m;
    Node<State, Selector> n_node;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.cplan = t[v].cplan;
    n_node.selector = selector;
    n_node.likelihood = t[v].likelihood;
    int w = boost::add_vertex(n_node, m);
    for (int i = 0; i < R; i++) {
      int n = cselection(m,w,eps,seed);
      seed++;
      if (m[n].tasks.empty()) {
          auto r = csimulation(m[n].state, m[n].tasks, domain, cfm, m[n].likelihood,max_likelihood,alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          cbackprop(m,n,r.first);
      }
      else {
        if (m[n].selector.sims == 0) {
          auto r = csimulation(m[n].state, m[n].tasks, domain, cfm, m[n].likelihood,max_likelihood,alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          cbackprop(m,n,r.first);
        }
        else {
          int n_p = cexpansion(m,n,domain,cfm,selector,max_likelihood,alpha,seed);
          seed++;
          auto r = csimulation(m[n_p].state, m[n_p].tasks, domain, cfm, m[n_p].likelihood,max_likelihood,alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          cbackprop(m,n_p,r.first);
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
    k.cplan = m[arg_max].cplan;
    k.selector = selector;
    k.depth = t[v].depth + 1;
    k.pred = v;
    k.likelihood = m[arg_max].likelihood;
    int y = boost::add_vertex(k, t);
    t[v].successors.push_back(y);
    seed++;
    v = y;
  }
  t[boost::graph_bundle].cplans.push_back(t[v].cplan);
  std::cout << "Plan found at depth " << t[v].depth << " and score of " << t[v].selector.rewardFunc(t[v].state);
  std::cout << " with likelihood " << t[v].likelihood << std::endl;
  std::cout << std::endl;
  std::cout << "Final State:" << std::endl;
  std::cout << t[v].state.to_json() << std::endl;
  std::cout << std::endl;
  return;

}

template <class State, class Domain, class Selector>
std::pair<Tree<State,Selector>,int> cppMCTShop(State state,
                  Tasks tasks,
                  Domain& domain,
                  CFM& cfm,
                  Selector selector,
                  int R,
                  double eps = 0.4,
                  double alpha = 0.5,
                  int seed = 4021) {
    Tree<State, Selector> t;
    Node<State, Selector> root;
    root.state = state;
    root.tasks = tasks;
    root.cplan = {};
    root.depth = 0;
    root.selector = selector;
    root.likelihood = 0.0;
    int v = boost::add_vertex(root, t);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    std::cout << t[v].state.to_json() << std::endl;
    std::cout << std::endl;
    cseek_planMCTS(t, v, domain, cfm, selector, R, eps, alpha, seed);
    std::cout << "Plan:" << std::endl;
    print(t[boost::graph_bundle].cplans.back());
    return std::make_pair(t,v);
}
