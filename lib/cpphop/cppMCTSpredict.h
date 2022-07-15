
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
struct ptNode {
    State state;
    Tasks tasks;
    Predictions predictions;
    int depth;
    double mean = 0.0;
    int sims = 0;
    double likelihood;
    int pred = -1;
    std::vector<int> successors = {};
};

template <class State>
struct ptTree {
  std::unordered_map<int,ptNode<State>> nodes;
  int nextID = 0;
  std::vector<int> freedIDs;
  int add_node(ptNode<State>& n) {
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
ptselection(ptTree<State>& t,
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
void ptbackprop(ptTree<State>& t, int n, double r) {
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
ptsimulation(Predictions predictions,
           State state,
           Tasks tasks,
           Domain& domain,
           CPM& cpm,
           double likelihood,
           double max_likelihood,
           double alpha,
           int seed) {
    while (!tasks.empty() && predictions.size() < state.agents.size()) {
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
              for (auto const &a : task.agents) {
                if (predictions.find(a) == predictions.end()) {
                  predictions.insert({a,task});
                } 
              }
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
int ptexpansion(ptTree<State>& t,
              int n,
              Domain& domain,
              CPM& cpm,
              double alpha,
              int seed = 4021) {
    Task task = t.nodes[n].tasks.back();

    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t.nodes[n].state, task.args);
        if (newstate) {
            pOperator<State> pop = domain.poperators[task.task_id];
            ptNode<State> v;
            v.state = newstate.value();
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.depth = t.nodes[n].depth + 1;
            v.predictions = t.nodes[n].predictions;
            for (auto const &a : task.agents) {
              if (v.predictions.find(a) == v.predictions.end()) {
                v.predictions.insert({a,task});
              }
            } 
            v.pred = n;
            v.likelihood = t.nodes[n].likelihood + log(pop(t.nodes[n].state,v.state,task.args));
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
          ptNode<State> v;
          if (m.first != "U") {
            if (cpm.find(key) != cpm.end()) {
              if (cpm[key].find(task.task_id) != cpm[key].end()) {
                if (cpm[key][task.task_id].find(m.first) != cpm[key][task.task_id].end()) {
                  v.likelihood = t.nodes[n].likelihood + log(cpm[key][task.task_id][m.first]); 
                }
                else {
                  v.likelihood = t.nodes[n].likelihood + log(alpha);
                }
              }
              else {
                v.likelihood = t.nodes[n].likelihood + log(alpha);
              }
            }
            else {
              v.likelihood = t.nodes[n].likelihood + log(alpha);
            }
          }
          else {
            v.likelihood = t.nodes[n].likelihood + log(1.0/c.size());
          }

          v.state = t.nodes[n].state;
          v.tasks = t.nodes[n].tasks;
          v.tasks.pop_back();
          v.depth = t.nodes[n].depth + 1;
          v.predictions = t.nodes[n].predictions;
          for (auto i = m.second.end();
              i != m.second.begin();) {
            v.tasks.push_back(*(--i));
          }
          v.pred = n;
          int w = t.add_node(v);
          t.nodes[n].successors.push_back(w);
          c_count.push_back(w);
        }
        seed++;
        if (c_count.empty()) {   
          std::cout << task.task_id << std::endl;
          return n;
        }
        int r = *select_randomly(c_count.begin(), c_count.end(), seed);
        return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

template <class State, class Domain>
Predictions
ptseek_planMCTS(ptTree<State>& t,
                 int v,
                 Domain& domain,
                 CPM& cpm,
                 int R = 30,
                 double eps = 0.4,
                 double alpha = 0.05,
                 int seed = 4021,
                 int aux_R = 10) {

  double max_likelihood = log(0.0);
  ptTree<State> m;
  ptNode<State> n_node;
  n_node.state = t.nodes[v].state;
  n_node.tasks = t.nodes[v].tasks;
  n_node.depth = t.nodes[v].depth;
  n_node.predictions = t.nodes[v].predictions;
  n_node.likelihood = t.nodes[v].likelihood;
  int w = m.add_node(n_node);
  while (!t.nodes[v].tasks.empty() && t.nodes[v].predictions.size() < t.nodes[v].state.agents.size()) {
    int aux = aux_R;
    for (int i = 0; i < R; i++) {
      int n = ptselection(m,w,eps,seed);
      seed++;
      if (m.nodes[n].tasks.empty()) {
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
          ptbackprop(m,n,r);
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = ptsimulation(m.nodes[n].predictions,
                               m.nodes[n].state, 
                               m.nodes[n].tasks, 
                               domain, 
                               cpm, 
                               m.nodes[n].likelihood,
                               max_likelihood,
                               alpha,
                               seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          ptbackprop(m,n,r.first);
        }
        else {
          int n_p = ptexpansion(m,n,domain,cpm,alpha,seed);
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
          auto r = ptsimulation(m.nodes[n_p].predictions,
                               m.nodes[n_p].state, 
                               m.nodes[n_p].tasks, 
                               domain, 
                               cpm, 
                               m.nodes[n_p].likelihood,
                               max_likelihood,
                               alpha,
                               seed);
          if (r.second > max_likelihood) {
            max_likelihood = r.second;
          }
          seed++;
          ptbackprop(m,n_p,r.first);
        }
      }
    }
    if (m.nodes[w].successors.empty()) {
      break;
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

    ptNode<State> k;
    k.state = m.nodes[arg_max].state;
    k.tasks = m.nodes[arg_max].tasks;
    k.predictions = m.nodes[arg_max].predictions;
    k.depth = t.nodes[v].depth + 1;
    k.pred = v;
    k.likelihood = m.nodes[arg_max].likelihood;
    int y = t.add_node(k);
    t.nodes[v].successors.push_back(y);
    seed++;
    v = y;

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

          ptNode<State> j;
          j.state = m.nodes[arg_max].state;
          j.tasks = m.nodes[arg_max].tasks;
          j.predictions = m.nodes[arg_max].predictions;
          j.depth = t.nodes[v].depth + 1;
          j.pred = v;
          j.likelihood = m.nodes[arg_max].likelihood;
          int y = t.add_node(j);
          t.nodes[v].successors.push_back(y);
          seed++;
          v = y;

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

            ptNode<State> j;
            j.state = m.nodes[arg_max].state;
            j.tasks = m.nodes[arg_max].tasks;
            j.predictions = m.nodes[arg_max].predictions;
            j.depth = t.nodes[v].depth + 1;
            j.pred = v;
            j.likelihood = m.nodes[arg_max].likelihood;
            int y = t.add_node(j);
            t.nodes[v].successors.push_back(y);
            seed++;
            v = y;
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
  return t.nodes[v].predictions;

}

template <class State, class Domain>
std::pair<ptTree<State>,int> 
cppMCTSpredict(State state,
           Tasks tasks,
           Domain& domain,
           CPM& cpm,
           int R,
           double eps = 0.4,
           double alpha = 0.05,
           int seed = 4021,
           int aux_R = 10) {
    ptTree<State> t;
    ptNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.predictions = {};
    root.depth = 0;
    root.likelihood = 0.0;
    int v = t.add_node(root);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    std::cout << t.nodes[v].state.to_json() << std::endl;
    std::cout << std::endl;
    auto predictions = ptseek_planMCTS(t, v, domain, cpm, R,eps, alpha, seed,aux_R);
    std::cout << "Predictions:" << std::endl;
    for (auto const &a : state.agents) {
      print(predictions.at(a));
    } 
    std::cout << std::endl;
    return std::make_pair(t,v);
}