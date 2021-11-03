#pragma once

#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include "../util.h"
#include <nlohmann/json.hpp>
#include <math.h>
#include <random>
#include <cfloat>

using json = nlohmann::json;

template <class State>
struct prNode {
    State state;
    Tasks tasks;
    json team_plan;
    CFM cfm;
    double mean = 0.0;
    int sims = 0;
    double likelihood;
    int pred = -1;
    std::vector<int> successors = {};
};

template <class State>
struct prTree {
  std::unordered_map<int,prNode<State>> nodes;
  int nextID = 0;
  std::vector<int> freedIDs; 
  int add_node(prNode<State>& n) {
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
tselection_rec(prTree<State>& t,
          int v,
          double eps,
          int seed = 2021) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<> dis(0.0,1.0);
    while (!t.nodes[v].successors.empty()) {
      double e = dis(gen);
      if (e > eps) {
        std::vector<double> r_maxes = {};
        r_maxes.push_back(t.nodes[v].successors.front());
        double r_max = t.nodes[r_maxes.back()].mean;
        for (auto const &w : t.nodes[v].successors) {
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
void tbackprop_rec(prTree<State>& t, int n, double r) {
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
std::pair<int,double>
tsimulation_rec(json& data_team_plan,
           json team_plan,
           State state,
           Tasks tasks,
           Domain& domain,
           CPM& cpm,
           double likelihood,
           double max_likelihood,
           int seed) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<double> dis(0.0,1.0);
    while (team_plan["size"] < data_team_plan["size"]) {
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
              json g;
              g["task"] = task2string(task);
              state = newstate.value();
              for (auto const &a : task.agents) {
                team_plan["plan"][a].push_back(g);
                team_plan["size"] = 1 + team_plan["size"].get<int>();
              }
              seed++;
              continue;
          }
          return std::make_pair(-1,log(0.0));
      }

      if (in(task.task_id, domain.cmethods)) {
        auto relevant = domain.cmethods[task.task_id];
        std::vector<cTasks> c = {};
        std::string key = "";
        for (auto const &cmethod : relevant) {
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
                cpm[key][task.task_id][r.first] = dis(gen); 
                likelihood = likelihood + log(cpm[key][task.task_id][r.first]);
              }
            }
            else {
              cpm[key][task.task_id][r.first] = dis(gen);
              likelihood = likelihood + log(cpm[key][task.task_id][r.first]);
            }
          }
          else {
            cpm[key][task.task_id][r.first] = dis(gen);
            likelihood = likelihood + log(cpm[key][task.task_id][r.first]);
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
    if (team_plan["plan"] == data_team_plan["plan"]) {
      if (likelihood < max_likelihood) {
        return std::make_pair(-1,likelihood);
      }
      if (likelihood == max_likelihood) {
        return std::make_pair(0,likelihood);
      }
      return std::make_pair(1,likelihood);
    }
    return std::make_pair(-1,log(0.0));
}

template <class State, class Domain>
int texpansion_rec(prTree<State>& t,
                  int n,
                  Domain& domain,
                  CPM& cpm,
                  int seed = 2021) {
    Task task = t.nodes[n].tasks.back();
    std::mt19937 gen(seed);
    std::uniform_real_distribution<double> dis(0.0,1.0);
    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t.nodes[n].state, task.args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task.task_id];
            prNode<State> v;
            v.state = newstate.value();
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.pred = n;
            v.likelihood = t.nodes[n].likelihood + log(pop(t.nodes[n].state,v.state,task.args)); 
            v.team_plan = t.nodes[n].team_plan;
            json g;
            g["task"] = task2string(task);
            for (auto const &a : task.agents) {
              v.team_plan["plan"][a].push_back(g);
              v.team_plan["size"] = 1 + v.team_plan["size"].template get<int>();
            }
            v.cfm = t.nodes[n].cfm;
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
        std::vector<cTasks> c = {};
        std::string key = "";
        for (auto const &cmethod : relevant) {
          cTasks subtasks = cmethod(t.nodes[n].state,task.args);
          if (subtasks.first != "NIL") {
            c.push_back(subtasks);
            key += subtasks.first + "#";
          }
        }
        
        std::vector<int> c_count = {};
        for (auto const &m : c) {
          prNode<State> v;
          if (m.first != "U") {
            if (cpm.find(key) != cpm.end()) {
              if (cpm[key].find(task.task_id) != cpm[key].end()) {
                if (cpm[key][task.task_id].find(m.first) != cpm[key][task.task_id].end()) {
                  v.likelihood = t.nodes[n].likelihood + log(cpm[key][task.task_id][m.first]);
                }
                else {
                  cpm[key][task.task_id][m.first] = dis(gen);
                  v.likelihood = t.nodes[n].likelihood + log(cpm[key][task.task_id][m.first]);
                }
              }
              else {
                cpm[key][task.task_id][m.first] = dis(gen);
                v.likelihood = t.nodes[n].likelihood + log(cpm[key][task.task_id][m.first]);
              }
            }
            else {
              cpm[key][task.task_id][m.first] = dis(gen);
              v.likelihood = t.nodes[n].likelihood + log(cpm[key][task.task_id][m.first]);
            }
          }
          else {
            v.likelihood = t.nodes[n].likelihood + log(1.0/c_count.size());
          }
          v.state = t.nodes[n].state;
          v.tasks = t.nodes[n].tasks;
          v.tasks.pop_back();
          v.team_plan = t.nodes[n].team_plan;
          for (auto i = m.second.end();
              i != m.second.begin();) {
            v.tasks.push_back(*(--i));
          }
          v.pred = n;
          v.cfm = t.nodes[n].cfm;
          if (m.first != "U") {
            if (v.cfm.find(key) != v.cfm.end()) {
              if (v.cfm[key].find(task.task_id) != v.cfm[key].end()) {
                if (v.cfm[key][task.task_id].find(m.first) != v.cfm[key][task.task_id].end()) {
                  v.cfm[key][task.task_id][m.first] += 1;
                }
                else {
                  v.cfm[key][task.task_id][m.first] = 1;
                }
              }
              else {
                v.cfm[key][task.task_id][m.first] = 1;
              }
            }
            else {
              v.cfm[key][task.task_id][m.first] = 1;
            }
          }
          int w = t.add_node(v);
          t.nodes[n].successors.push_back(w);
          c_count.push_back(w);
        }
        seed++;
        if (c_count.empty()) {   
          return n;
        }
        auto r = *select_randomly(c_count.begin(), c_count.end(), seed);
        return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain>
CFM
train_planrecMCTS(json& data_team_plan,
                 prNode<State> v,
                 Domain& domain,
                 CPM& cpm,
                 int R = 30,
                 double eps = 0.4,
                 int seed = 2021,
                 int aux_R = 10) {
  double max_likelihood = log(0.0);
  prTree<State> m;
  prNode<State> n_node;
  n_node.state = v.state;
  n_node.tasks = v.tasks;
  n_node.cfm = v.cfm;
  n_node.team_plan = v.team_plan;
  n_node.likelihood = v.likelihood;
  int w = m.add_node(n_node);
  while (v.team_plan["size"] < data_team_plan["size"]) {
    int aux = aux_R;
    for (int i = 0; i < R; i++) {
      int n = tselection_rec(m,w,eps,seed);
      seed++;
      if (m.nodes[n].team_plan["size"] >= data_team_plan["size"]) {
        if (m.nodes[n].team_plan["plan"] == data_team_plan["plan"]) {
          int r;
          if (m.nodes[n].likelihood < max_likelihood) {
            r = -1;
          }
          if (m.nodes[n].likelihood == max_likelihood) {
            r = 0;
          }
          if (m.nodes[n].likelihood > max_likelihood) {
            r = 1; 
            max_likelihood = m.nodes[n].likelihood;
          }
          tbackprop_rec(m,n,r);
        }
        tbackprop_rec(m,n,-1);
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = tsimulation_rec(data_team_plan,m.nodes[n].team_plan,m.nodes[n].state, m.nodes[n].tasks, domain, cpm, m.nodes[n].likelihood, max_likelihood,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          tbackprop_rec(m,n,r.first);
        }
        else {
          int n_p = texpansion_rec(m,n,domain,cpm,seed);
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
          auto r = tsimulation_rec(data_team_plan,m.nodes[n].team_plan,m.nodes[n].state, m.nodes[n].tasks, domain, cpm, m.nodes[n].likelihood, max_likelihood,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          tbackprop_rec(m,n_p,r.first);   
        }
      }
    }
    //Mandatory step
    int arg_max = m.nodes[w].successors.front();
    double max = m.nodes[arg_max].mean;
    for (auto const &s : m.nodes[w].successors) {
        double mean = m.nodes[s].mean;
        if (mean > max) {
            max = mean;
            arg_max = s;
        }
    }
    //Clean Up
    for (auto const &s : m.nodes[w].successors) {
      if (s != arg_max) {
        m.delete_nodes(s);
      }
    }
    m.delete_node(w);
    m.nodes[arg_max].pred = -1;
    
    //Try to step again
    if (!m.nodes[arg_max].successors.empty()) {
      std::mt19937 gen(seed);
      std::uniform_real_distribution<double> dis(0.0,1.0);
      bool step_again;
      do {
        if (m.nodes[arg_max].successors.size() == 1) {
          step_again = true;
          int new_arg_max = m.nodes[arg_max].successors.front();
          m.delete_node(arg_max);
          m.nodes[new_arg_max].pred = -1;
          arg_max = new_arg_max;
        }
        else {
          int new_arg_max = m.nodes[arg_max].successors.front();
          double max = m.nodes[new_arg_max].mean;
          for (auto const &s : m.nodes[arg_max].successors) {
            double mean = m.nodes[s].mean;
            if (mean > max) {
              max = mean;
              new_arg_max = s;
            }
          }
          double e = dis(gen); 
          if (e <= exp(-(1.0/m.nodes[new_arg_max].sims))) {
            step_again = true;
            for (auto const &s : m.nodes[arg_max].successors) {
              if (s != new_arg_max) {
                m.delete_nodes(s);
              }
            }
            m.delete_node(arg_max);
            m.nodes[new_arg_max].pred = -1;
            arg_max = new_arg_max;
          }
          else {
            step_again = false;
          }
        }
      } while (step_again && !m.nodes[arg_max].successors.empty());
    }
    w = arg_max;
    seed++;
  }
  return m.nodes[w].cfm;
 
}

template <class State, class Domain>
CFM 
cppMCTStrain(json& data_team_plan,
                  State state,
                  Tasks tasks,
                  Domain& domain,
                  CPM& cpm,
                  int R = 30,
                  double eps = 0.4,
                  int seed = 2021,
                  int aux_R = 10) {
    prNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.likelihood = 0.0;
    root.team_plan["size"] = 0;
    return train_planrecMCTS(data_team_plan,root, domain, cpm, R, eps, seed);
}
