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
    double mean = 0.0;
    int sims = 0;
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
};

template <class State>
struct prResults {
  prTree<State> t;
  int root;
  int end;
};

bool subseq(json& j, json& g) {
  for (int t = 0; t < j.size(); t++) {
    if (j[t] != g[t]) {
      return false;
    }
  }
  return true;
}

bool subsequence(json& j, json& g, std::vector<std::string>& agents) {

  for (auto const &a : agents) {
    if (j["plan"][a].size() <= g["plan"][a].size()) {
      if (!subseq(j["plan"][a], g["plan"][a])) {
        return false;
      }
    }
    else {
      return false;
    }
  }
  return true;
}

template <class State>
int
cselection_rec(prTree<State>& t,
          int v,
          double eps,
          int seed = 2021) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<double> dis(0.0,1.0);
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
void cbackprop_rec(prTree<State>& t, int n, double r) {
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
csimulation_rec(int horizon,
           json& data_team_plan,
           json team_plan,
           State state,
           Tasks tasks,
           Domain& domain,
           int seed) {

    int h = 0;
    while (team_plan["size"] < data_team_plan["size"] && h < horizon) {
      Task task = tasks.back();

      if (in(task.task_id, domain.operators)) {
          Operator<State> op = domain.operators[task.task_id];
          std::optional<State> newstate = op(state, task.args);
          if (newstate) {
              pOperator<State> pop = domain.poperators[task.task_id];
              tasks.pop_back();
              json g;
              g["task"] = task2string(task);
              state = newstate.value();
              for (auto const &a : task.agents) {
                team_plan["plan"][a].push_back(g);
                team_plan["size"] = 1 + team_plan["size"].get<int>();
              }
              seed++;
              h++;
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
        h++;
        continue;  
      }
      std::string message = "Invalid task ";
      message += task.task_id;
      message += " during simulation!";
      throw std::logic_error(message);
    }
    if (subsequence(team_plan, data_team_plan, state.agents)) {
      return domain.score(state);
    }
    return 0.0;
}

template <class State, class Domain>
int cexpansion_rec(prTree<State>& t,
                  int n,
                  Domain& domain,
                  int seed = 2021) {

    Task task = t.nodes[n].tasks.back();
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
            v.team_plan = t.nodes[n].team_plan;
            json g;
            g["task"] = task2string(task);
            for (auto const &a : task.agents) {
              v.team_plan["plan"][a].push_back(g);
              v.team_plan["size"] = 1 + v.team_plan["size"].template get<int>();
            }
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
            prNode<State> v;
            v.state = t.nodes[n].state;
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.team_plan = t.nodes[n].team_plan;
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
        //std::cout << total << std::endl;
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
int
cseek_planrecMCTS(json& data_team_plan,
                 prTree<State>& t,
                 int v,
                 Domain& domain,
                 int R = 30,
                 double eps = 0.4,
                 int seed = 2021,
                 int aux_R = 10) {

  std::mt19937 gen(seed);
  std::negative_binomial_distribution<int> nbd(50,0.75);
  while (t.nodes[v].team_plan["size"] < data_team_plan["size"]) {
    prTree<State> m;
    prNode<State> n_node;
    n_node.state = t.nodes[v].state;
    n_node.tasks = t.nodes[v].tasks;
    n_node.team_plan = t.nodes[v].team_plan;
    int w = m.add_node(n_node);
    int aux = aux_R;
    int hzn = nbd(gen);
    for (int i = 0; i < R; i++) {
      int n = cselection_rec(m,w,eps,seed);
      seed++;
      if (m.nodes[n].team_plan["size"] >= data_team_plan["size"]) {
          if (m.nodes[n].team_plan["plan"] == data_team_plan["plan"]) {
            cbackprop_rec(m,n,domain.score(m.nodes[n].state));
          }
          else {
            cbackprop_rec(m,n,0.0);
          }
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = csimulation_rec(hzn,
                                   data_team_plan,
                                   m.nodes[n].team_plan,
                                   m.nodes[n].state, 
                                   m.nodes[n].tasks, 
                                   domain, 
                                   seed);
          seed++;
          cbackprop_rec(m,n,r);
        }
        else {
          int n_p = cexpansion_rec(m,n,domain,seed);
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
          auto r = csimulation_rec(hzn, 
                                   data_team_plan, 
                                   m.nodes[n_p].team_plan, 
                                   m.nodes[n_p].state, 
                                   m.nodes[n_p].tasks, 
                                   domain, 
                                   seed);
          seed++;
          cbackprop_rec(m,n_p,r);   
        }
      }
    }

    int arg_max = m.nodes[w].successors.front();
    double max = m.nodes[arg_max].mean;
    for (int s : m.nodes[w].successors) {
        double mean = m.nodes[s].mean;
        if (mean > max) {
            max = mean;
            arg_max = s;
        }
    }

    prNode<State> k;
    k.state = m.nodes[arg_max].state;
    k.tasks = m.nodes[arg_max].tasks;
    k.team_plan = m.nodes[arg_max].team_plan;
    k.pred = v;
    int y = t.add_node(k);
    t.nodes[v].successors.push_back(y);
    seed++;
    v = y;

    while (m.nodes[arg_max].successors.size() == 1) {
      arg_max = m.nodes[arg_max].successors.front();
      prNode<State> j;
      j.state = m.nodes[arg_max].state;
      j.tasks = m.nodes[arg_max].tasks;
      j.team_plan = m.nodes[arg_max].team_plan;
      j.pred = v;
      int y = t.add_node(j);
      t.nodes[v].successors.push_back(y);
      seed++;
      v = y;
    }
          
  }
  return v;
 
}

template <class State, class Domain>
prResults<State> 
cppMCTSplanrec(json& data_team_plan,
                  State state,
                  Tasks tasks,
                  Domain& domain,
                  int R = 30,
                  double eps = 0.4,
                  int seed = 2021,
                  int aux_R = 10) {
    prTree<State> t;
    prNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.team_plan["size"] = 0;
    int v = t.add_node(root);
    int w = cseek_planrecMCTS(data_team_plan,t, v, domain, R, eps, seed);
    prResults<State> prr;
    prr.t = t;
    prr.root = v;
    prr.end = w;
    return prr;
}
