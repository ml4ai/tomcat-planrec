
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

};

template <class State>
int
ptselection(ptTree<State>& t,
          int v,
          double eps,
          int seed = 4021) {

    std::mt19937 gen(seed);
    std::uniform_real_distribution<double> dis(0.0,1.0);
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
double
ptsimulation(int horizon,
             State state,
             Tasks tasks,
             Domain& domain,
             int seed) {
    int h = 0;
    while (!tasks.empty() && h < horizon) {
      Task task = tasks.back();

      if (in(task.task_id, domain.operators)) {
          Operator<State> op = domain.operators[task.task_id];
          std::optional<State> newstate = op(state, task.args);
          if (newstate) {
              tasks.pop_back();
              seed++;
              state = newstate.value();
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
    return domain.score(state);
}

template <class State, class Domain>
int ptexpansion(ptTree<State>& t,
              int n,
              Domain& domain,
              int seed = 4021) {
    Task task = t.nodes[n].tasks.back();

    if (in(task.task_id, domain.operators)) {
        Operator<State> op = domain.operators[task.task_id];
        std::optional<State> newstate = op(t.nodes[n].state, task.args);
        if (newstate) {
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
            ptNode<State> v;
            v.state = t.nodes[n].state;
            v.tasks = t.nodes[n].tasks;
            v.tasks.pop_back();
            v.depth = t.nodes[n].depth + 1;
            v.predictions = t.nodes[n].predictions;
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
Predictions
ptseek_planMCTS(ptTree<State>& t,
                 int v,
                 Domain& domain,
                 int R = 30,
                 double eps = 0.4,
                 int seed = 4021,
                 int aux_R = 10) {

  std::mt19937 gen(seed);
  std::negative_binomial_distribution<int> nbd(50,0.75);
  while (!t.nodes[v].tasks.empty() && t.nodes[v].predictions.size() < t.nodes[v].state.agents.size()) {
    ptTree<State> m;
    ptNode<State> n_node;
    n_node.state = t.nodes[v].state;
    n_node.tasks = t.nodes[v].tasks;
    n_node.depth = t.nodes[v].depth;
    n_node.predictions = t.nodes[v].predictions;
    int w = m.add_node(n_node);
    int hzn = nbd(gen);
    int aux = aux_R;
    for (int i = 0; i < R; i++) {
      int n = ptselection(m,w,eps,seed);
      seed++;
      if (m.nodes[n].tasks.empty()) {
        ptbackprop(m,n,domain.score(m.nodes[n].state));
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = ptsimulation(hzn,
                               m.nodes[n].state, 
                               m.nodes[n].tasks, 
                               domain, 
                               seed);
          seed++;
          ptbackprop(m,n,r);
        }
        else {
          int n_p = ptexpansion(m,n,domain,seed);
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
          auto r = ptsimulation(hzn,
                               m.nodes[n_p].state, 
                               m.nodes[n_p].tasks, 
                               domain, 
                               seed);
          seed++;
          ptbackprop(m,n_p,r);
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

    ptNode<State> k;
    k.state = m.nodes[arg_max].state;
    k.tasks = m.nodes[arg_max].tasks;
    k.predictions = m.nodes[arg_max].predictions;
    k.depth = t.nodes[v].depth + 1;
    k.pred = v;
    int y = t.add_node(k);
    t.nodes[v].successors.push_back(y);
    seed++;
    v = y;

    while (m.nodes[arg_max].successors.size() == 1) {
      arg_max = m.nodes[arg_max].successors.front();

      ptNode<State> j;
      j.state = m.nodes[arg_max].state;
      j.tasks = m.nodes[arg_max].tasks;
      j.predictions = m.nodes[arg_max].predictions;
      j.depth = t.nodes[v].depth + 1;
      j.pred = v;
      int y = t.add_node(j);
      t.nodes[v].successors.push_back(y);
      seed++;
      v = y;
    }
    seed++;
  }
  return t.nodes[v].predictions;

}

template <class State, class Domain>
std::pair<ptTree<State>,int> 
cppMCTSpredict(State state,
           Tasks tasks,
           Domain& domain,
           int R,
           double eps = 0.4,
           int seed = 4021,
           int aux_R = 10) {
    ptTree<State> t;
    ptNode<State> root;
    root.state = state;
    root.tasks = tasks;
    root.predictions = {};
    root.depth = 0;
    int v = t.add_node(root);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    std::cout << t.nodes[v].state.to_json() << std::endl;
    std::cout << std::endl;
    auto predictions = ptseek_planMCTS(t, v, domain, R, eps, seed, aux_R);
    std::cout << "Predictions:" << std::endl;
    for (auto const &a : state.agents) {
      print(predictions.at(a));
    } 
    std::cout << std::endl;
    return std::make_pair(t,v);
}
