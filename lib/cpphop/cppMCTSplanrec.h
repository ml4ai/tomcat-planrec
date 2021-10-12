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
    double likelihood;
    int pred = -1;
    std::vector<int> successors = {};
};

template <class State>
using prTree = std::vector<prNode<State>>;

template <class State>
int add_node(prNode<State>& n,prTree<State>& t) {
  t.push_back(n);
  return t.size() - 1;
}

template <class State>
int
cselection_rec(prTree<State>& t,
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
void cbackprop_rec(prTree<State>& t, int n, double r) {
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
csimulation_rec(json& data_team_plan,
           json team_plan,
           State state,
           Tasks tasks,
           Domain& domain,
           CFM& cfm,
           double likelihood,
           double max_likelihood,
           double alpha,
           int seed) {

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
              for (auto a : task.agents) {
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
int cexpansion_rec(prTree<State>& t,
                  int n,
                  Domain& domain,
                  CFM& cfm,
                  double alpha,
                  int seed = 2021) {
    Task task = t[n].tasks.back();

    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t[n].state, task.args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task.task_id];
            prNode<State> v;
            v.state = newstate.value();
            v.tasks = t[n].tasks;
            v.tasks.pop_back();
            v.pred = n;
            v.likelihood = t[n].likelihood + log(pop(t[n].state,v.state,task.args)); 
            v.team_plan = t[n].team_plan;
            json g;
            g["task"] = task2string(task);
            for (auto a : task.agents) {
              v.team_plan["plan"][a].push_back(g);
              v.team_plan["size"] = 1 + v.team_plan["size"].template get<int>();
            }
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
          prNode<State> v;
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
          v.team_plan = t[n].team_plan;
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
void
cseek_planrecMCTS(json& data_team_plan,
                 prTree<State>& t,
                 int v,
                 Domain& domain,
                 CFM& cfm,
                 int R = 30,
                 double eps = 0.4,
                 double alpha = 0.5,
                 int seed = 2021,
                 int aux_R = 10) {
  double max_likelihood = log(0.0);
  while (t[v].team_plan["size"] < data_team_plan["size"]) {
    prTree<State> m;
    prNode<State> n_node;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.team_plan = t[v].team_plan;
    n_node.likelihood = t[v].likelihood;
    int w = add_node(n_node, m);
    int aux = aux_R;
    for (int i = 0; i < R; i++) {
      int n = cselection_rec(m,w,eps,seed);
      seed++;
      if (m[n].team_plan["size"] >= data_team_plan["size"]) {
        if (m[n].team_plan["plan"] == data_team_plan["plan"]) {
          int r;
          if (m[n].likelihood < max_likelihood) {
            r = -1;
          }
          if (m[n].likelihood == max_likelihood) {
            r = 0;
          }
          if (m[n].likelihood > max_likelihood) {
            r = 1; 
            max_likelihood = m[n].likelihood;
          }
          cbackprop_rec(m,n,r);
        }
        cbackprop_rec(m,n,-1);
      }
      else {
        if (m[n].sims == 0) {
          auto r = csimulation_rec(data_team_plan,m[n].team_plan,m[n].state, m[n].tasks, domain, cfm, m[n].likelihood, max_likelihood, alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          cbackprop_rec(m,n,r.first);
        }
        else {
          int n_p = cexpansion_rec(m,n,domain,cfm,alpha,seed);
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
          auto r = csimulation_rec(data_team_plan,m[n].team_plan,m[n].state, m[n].tasks, domain, cfm, m[n].likelihood, max_likelihood, alpha,seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          cbackprop_rec(m,n_p,r.first);   
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
    prNode<State> k;
    k.state = m[arg_max].state;
    k.tasks = m[arg_max].tasks;
    k.team_plan = m[arg_max].team_plan;
    k.pred = v;
    k.likelihood = m[arg_max].likelihood;
    int y = add_node(k, t);
    t[v].successors.push_back(y);
    seed++;
    v = y;
  }
  return;
 
}

template <class State, class Domain>
std::pair<prTree<State>,int> 
cppMCTSplanrec(json& data_team_plan,
                  State state,
                  Tasks tasks,
                  Domain& domain,
                  CFM& cfm,
                  int R = 30,
                  double eps = 0.4,
                  double alpha = 0.5,
                  int seed = 2021,
                  int aux_R = 10) {
    prTree<State> t;
    prNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.likelihood = 0.0;
    root.team_plan["size"] = 0;
    int v = add_node(root, t);
    cseek_planrecMCTS(data_team_plan,t, v, domain, cfm, R, eps, alpha, seed);
    return std::make_pair(t,v);
}
