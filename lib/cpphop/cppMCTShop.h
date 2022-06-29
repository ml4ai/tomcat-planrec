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
    int pred = -1;
    std::vector<int> successors = {};
};

template <class State>
struct pTree {
  std::unordered_map<int,pNode<State>> nodes;
  int nextID = 0;
  std::vector<int> freedIDs;
  int add_node(pNode<State>& n) {
    int id;
    if (!freedIDs.empty()) {
      id = freedIDs.back();
      freedIDs.pop_back();
    }
    else {
      id = nextID;
      nextID++;
    }
    nodes[id] = n;
    return id;
  }
  void delete_node(int id) {
    if (nodes.erase(id)) {
      freedIDs.push_back(id);
    }
    return;
  }

  void delete_nodes(int root_id) {
    if (!nodes[root_id].successors.empty()) {
      for (auto const &x : nodes[root_id].successors) {
        delete_nodes(x);
      }
    }
    delete_node(root_id);
    return;
  }
};

template <class State>
int
cselection(pTree<State>& t,
          int v,
          double eps,
          int seed = 4021) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<> dis(0.0,1.0);
    while (!t.nodes[v].successors.empty()) {
      double e = dis(gen);
      if (e > eps) {
        std::vector<double> r_maxes = {};
        r_maxes.push_back(t.nodes[v].successors.front());
        double r_max = t.nodes[r_maxes.back()].mean;
        for (auto const & w : t.nodes[v].successors) {
            if (t.nodes[w].sims == 0) {
              return w;
            }
            double s = t.nodes[w].mean;
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
        int v_max = t.nodes[v_maxes.back()].sims;
        for (auto const &w : r_maxes) {
          int s = t.nodes[w].sims;
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
        for (auto const &w : t.nodes[v].successors) {
          if (t.nodes[w].sims == 0) {
            return w;
          }
        }
        seed++;
        v = *select_randomly(t.nodes[v].successors.begin(), t.nodes[v].successors.end(), seed);
        seed++;
      }
    }
    return v;
}

template <class State>
void cbackprop(pTree<State>& t, int n, double r) {
  do {
    if (t.nodes[n].successors.empty()) {
      t.nodes[n].mean = r;
      t.nodes[n].sims++;
    }
    else {
      t.nodes[n].mean = (r + t.nodes[n].sims*t.nodes[n].mean)/(t.nodes[n].sims + 1);
      t.nodes[n].sims++;
    }
    n = t.nodes[n].pred;
  }
  while (n != -1);
  return;
}

template <class State, class Domain>
double
csimulation(int horizon,
           State state,
           Tasks tasks,
           Domain& domain,
           int seed) {

    int i = 0;
    double int_score = domain.score(state);
    while (!tasks.empty() && i < horizon) {
      Task task = tasks.back();

      if (in(task.task_id, domain.operators)) {
          Operator<State> op = domain.operators[task.task_id];
          std::optional<State> newstate = op(state, task.args);
          if (newstate) {
              tasks.pop_back();
              seed++;
              state = newstate.value();
              i++;
              continue;
          }
          return 0.0;
      }

      if (in(task.task_id, domain.cmethods)) {
          auto relevant = domain.cmethods[task.task_id];
          std::vector<cTasks> c = {};
          for (auto const &cmethod : relevant) {
              cTasks subtasks = cmethod(state, task.args);
              if (subtasks.first != "NIL") {
                c.push_back(subtasks);
              }
          }
          seed++;
          if (c.empty()) {
            return 0.0;
          }
          cTasks r = *select_randomly(c.begin(), c.end(), seed);
          seed++;
          tasks.pop_back();
          for (auto i = r.second.end();
              i != r.second.begin();) {
            tasks.push_back(*(--i));
          }
          i++;
          continue;
      }
      std::string message = "Invalid task ";
      message += task.task_id;
      message += " during simulation!";
      throw std::logic_error(message);
    }
    double new_score = domain.score(state);
    if (int_score == 0.0) {
      if (new_score == 0.0) {
        return 0.0;
      }
      return 1.0;
    }
    double p_inc = (new_score - int_score)/int_score;
    if (p_inc > 1) {
      return 1;
    }
    return p_inc;
}

template <class State, class Domain>
int cexpansion(pTree<State>& t,
              int n,
              Domain& domain,
              int seed = 4021) {
    Task task = t.nodes[n].tasks.back();

    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t.nodes[n].state, task.args);
        if (newstate) {
            pNode<State> v;
            v.state = newstate.value();
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.depth = t.nodes[n].depth + 1;
            v.cplan = t.nodes[n].cplan;
            v.cplan.second.push_back(task);
            v.pred = n;
            int w = t.add_node(v);
            t.nodes[n].successors.push_back(w);
            return w;
        }
        std::string message = task.task_id;
        message += " preconditions failed during expansion!";
        throw std::logic_error(
            message);
    }

    if (in(task.task_id, domain.cmethods)) {
        auto relevant = domain.cmethods[task.task_id];
        std::vector<int> c = {};
        for (auto const &cmethod : relevant) {
          cTasks subtasks = cmethod(t.nodes[n].state,task.args);
          if (subtasks.first != "NIL") {
            pNode<State> v;
            v.state = t.nodes[n].state;
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.depth = t.nodes[n].depth + 1;
            v.cplan = t.nodes[n].cplan;
            for (auto i = subtasks.second.end();
                i != subtasks.second.begin();) {
              v.tasks.push_back(*(--i));
            }
            v.pred = n;
            int w = t.add_node(v);
            t.nodes[n].successors.push_back(w);
            c.push_back(w);
          }
        }
        seed++;
        if (c.empty()) {   
          std::cout << task.task_id << std::endl;
          return n;
        }
        int r = *select_randomly(c.begin(), c.end(), seed);
        return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain>
cTasks
cseek_planMCTS(pTree<State>& t,
                 int v,
                 Domain& domain,
                 int R = 30,
                 int plan_size = -1,
                 double eps = 0.4,
                 int seed = 4021,
                 int aux_R = 10) {

  pTree<State> m;
  pNode<State> n_node;
  n_node.state = t.nodes[v].state;
  n_node.tasks = t.nodes[v].tasks;
  n_node.depth = t.nodes[v].depth;
  n_node.cplan = t.nodes[v].cplan;
  int w = m.add_node(n_node);
  std::mt19937 gen(seed);
  std::negative_binomial_distribution<int> nbd(50,0.75);
  while (!t.nodes[v].tasks.empty()) {
    int aux = aux_R;
    int hzn = nbd(gen);
    for (int i = 0; i < R; i++) {
      int n = cselection(m,w,eps,seed);
      seed++;
      if (m.nodes[n].tasks.empty()) {
          cbackprop(m,n,0.0);
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = csimulation(hzn,
                               m.nodes[n].state, 
                               m.nodes[n].tasks, 
                               domain, 
                               seed);
          seed++;
          cbackprop(m,n,r);
        }
        else {
          int n_p = cexpansion(m,n,domain,seed);
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
          auto r = csimulation(hzn,
                               m.nodes[n_p].state, 
                               m.nodes[n_p].tasks, 
                               domain, 
                               seed);
          seed++;
          cbackprop(m,n_p,r);
        }
      }
    }

    int arg_max = m.nodes[w].successors.front();
    double max = m.nodes[arg_max].mean;
    for (auto const &s : m.nodes[w].successors) {
        double mean = m.nodes[s].mean;
        if (mean > max) {
            max = mean;
            arg_max = s;
        }
    }

    for (auto const &s : m.nodes[w].successors) {
      if (s != arg_max) {
        m.delete_nodes(s);
      }
    }
    m.delete_node(w);
    m.nodes[arg_max].pred = -1;

    pNode<State> k;
    k.state = m.nodes[arg_max].state;
    k.tasks = m.nodes[arg_max].tasks;
    k.cplan = m.nodes[arg_max].cplan;
    k.depth = t.nodes[v].depth + 1;
    k.pred = v;
    int y = t.add_node(k);
    t.nodes[v].successors.push_back(y);
    seed++;
    v = y;
    if (t.nodes[v].cplan.second.size() >= plan_size && plan_size != -1) {
      break;
    }
      
    bool plan_break = false;
    while (m.nodes[arg_max].successors.size() == 1) {
      int new_arg_max = m.nodes[arg_max].successors.front();
      m.delete_node(arg_max);
      m.nodes[new_arg_max].pred = -1;
      arg_max = new_arg_max;

      pNode<State> j;
      j.state = m.nodes[arg_max].state;
      j.tasks = m.nodes[arg_max].tasks;
      j.cplan = m.nodes[arg_max].cplan;
      j.depth = t.nodes[v].depth + 1;
      j.pred = v;
      int y = t.add_node(j);
      t.nodes[v].successors.push_back(y);
      seed++;
      v = y;

      if (t.nodes[v].cplan.second.size() >= plan_size && plan_size != -1) {
        plan_break = true;
        break;
      }
    }
    if (plan_break) {
      break;
    }
    w = arg_max;
    seed++;
  }
  std::cout << "Plan found at depth " << t.nodes[v].depth;
  std::cout << std::endl;
  std::cout << "Final State:" << std::endl;
  std::cout << t.nodes[v].state.to_json() << std::endl;
  std::cout << std::endl;
  return t.nodes[v].cplan;

}

template <class State, class Domain>
std::pair<pTree<State>,int> 
cppMCTShop(State state,
           Tasks tasks,
           Domain& domain,
           int R,
           int plan_size = -1,
           double eps = 0.4,
           int seed = 4021,
           int aux_R = 10) {
    pTree<State> t;
    pNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.cplan = {};
    root.depth = 0;
    int v = t.add_node(root);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    std::cout << t.nodes[v].state.to_json() << std::endl;
    std::cout << std::endl;
    auto plan = cseek_planMCTS(t, v, domain, R, plan_size, eps, seed, aux_R);
    std::cout << "Plan:" << std::endl;
    print(plan);
    return std::make_pair(t,v);
}
