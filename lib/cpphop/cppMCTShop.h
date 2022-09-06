#pragma once

#include "../util.h"
#include "../typedefs.h"
//#include "printing.h"
#include <any>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include <limits>

struct pNode {
    KnowledgeBase state;
    Grounded_Tasks tasks;
    std::vector<std::string> plan;
    int depth;
    double mean = 0.0;
    int sims = 0;
    int pred = -1;
    bool deadend = false;
    std::vector<int> successors = {};
};

struct pTree {
  std::unordered_map<int,pNode> nodes;
  int nextID = 0;
  std::vector<int> freedIDs;
  int add_node(pNode& n) {
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

int
cselection(pTree& t,
          int v,
          double eps,
          std::mt19937_64& g) {

    std::uniform_real_distribution<> dis(0.0,1.0);
    int original = v;
    while (!t.nodes[v].successors.empty()) {
      if (t.nodes[v].deadend) {
        return v;
      }
      double e = dis(g);
      if (e > eps) {
        std::vector<int> r_maxes = {};
        double r_max = -std::numeric_limits<double>::infinity();
        for (auto const &w : t.nodes[v].successors) {
          if (!t.nodes[w].deadend) {
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
        }
        if (r_maxes.empty()) {
          t.nodes[v].deadend = true;
          v = original;
          continue;
        }
        std::vector<int> v_maxes = {};
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
        v = *select_randomly(v_maxes.begin(), v_maxes.end(), g);
      }
      else {
        bool all_deadends = true;
        for (auto const &w : t.nodes[v].successors) {
          if (!t.nodes[w].deadend) {
            if (t.nodes[w].sims == 0) {
              return w;
            }
            all_deadends = false;
          }
        }
        if (all_deadends) {
          t.nodes[v].deadend = true;
          v = original;
          continue;
        }
        v = *select_randomly(t.nodes[v].successors.begin(), t.nodes[v].successors.end(), g);
      }
    }
    return v;
}

void cbackprop(pTree& t, int n, double r) {
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

double
csimulation(int horizon,
           KnowledgeBase state,
           Grounded_Tasks tasks,
           DomainDef& domain,
           std::mt19937_64& g,
           int h = 0) {
  if (tasks.empty() || h >= horizon) {
    return domain.score(state);
  }
  Grounded_Task task = tasks.back();
  h++;
  if (domain.actions.contains(task.first)) {
    auto act = domain.actions.at(task.first).apply(state,task.second);
    if (!act.second.empty()) {
      std::shuffle(act.second.begin(),act.second.end(),g);
      tasks.pop_back();
      for (auto &ns : act.second) {
        ns.update_state();
        double rs = csimulation(horizon,ns,tasks,domain,g,h);
        if (rs > -1.0) {
          return rs;
        }
      }
    }
    return -1.0;
  }

  if (domain.methods.contains(task.first)) {
    auto task_methods = domain.methods[task.first];
    std::shuffle(task_methods.begin(),task_methods.end(),g);
    for (auto &m : task_methods) {
      auto all_gts = m.apply(state,task.second);
      if (!all_gts.second.empty()) {
        std::shuffle(all_gts.second.begin(),all_gts.second.end(),g);
        tasks.pop_back();
        for (auto const& gts : all_gts.second) {
          tasks = merge_vec(tasks,gts);
          double rs = csimulation(horizon,state,tasks,domain,g,h);
          if (rs > -1.0) {
            return rs;
          }
        }
      }
    }
    return -1.0;
  }
  std::string message = "Invalid task ";
  message += task.first;
  message += " during simulation!";
  throw std::logic_error(message);
}

int cexpansion(pTree& t,
              int n,
              DomainDef& domain,
              std::mt19937_64& g) {
    Grounded_Task task = t.nodes[n].tasks.back();
    if (domain.actions.contains(task.first)) {
      auto act = domain.actions.at(task.first).apply(t.nodes[n].state,task.second);
      if (!act.second.empty()) {
        std::vector<int> a;
        for (auto const& state : act.second) {
          pNode v;
          v.state = state;
          v.state.update_state();
          v.tasks = t.nodes[n].tasks;
          v.tasks.pop_back();
          v.depth = t.nodes[n].depth + 1;
          v.plan = t.nodes[n].plan;
          v.plan.push_back(act.first);
          v.pred = n;
          int w = t.add_node(v);
          t.nodes[n].successors.push_back(w);
          a.push_back(w);
        }
        int r = *select_randomly(a.begin(), a.end(), g);
        return r;
      }
      t.nodes[n].deadend = true;
      return n;
    }

    if (domain.methods.contains(task.first)) {
      std::vector<int> choices;
      for (auto &m : domain.methods[task.first]) {
        auto gts = m.apply(t.nodes[n].state,task.second);
        for (auto const& g : gts.second) { 
          pNode v;
          v.state = t.nodes[n].state;
          v.tasks = t.nodes[n].tasks;
          v.tasks.pop_back();
          v.depth = t.nodes[n].depth + 1;
          v.plan = t.nodes[n].plan;
          v.tasks = merge_vec(v.tasks,g);
          v.pred = n;
          int w = t.add_node(v);
          t.nodes[n].successors.push_back(w);
          choices.push_back(w);
        }
      }
      if (choices.empty()) {
        t.nodes[n].deadend = true;
        return n;
      }
      int r = *select_randomly(choices.begin(), choices.end(), g);
      return r;
    }
    throw std::logic_error("Invalid task during expansion!");
}

int
cseek_planMCTS(pTree& t,
                 int v,
                 DomainDef& domain,
                 int R,
                 int plan_size,
                 double eps,
                 int successes,
                 double prob,
                 std::mt19937_64& g) {

  std::negative_binomial_distribution<int> nbd(successes,prob);
  int prev_v;
  while (!t.nodes[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.state = t.nodes[v].state;
    n_node.tasks = t.nodes[v].tasks;
    n_node.depth = t.nodes[v].depth;
    n_node.plan = t.nodes[v].plan;
    int w = m.add_node(n_node);
    int hzn = nbd(g);
    for (int i = 0; i < R; i++) {
      int n = cselection(m,w,eps,g);
      if (m.nodes[n].tasks.empty()) {
          cbackprop(m,n,domain.score(m.nodes[n].state));
      }
      else {
        if (m.nodes[n].sims == 0) {
          auto r = csimulation(hzn,
                               m.nodes[n].state, 
                               m.nodes[n].tasks, 
                               domain,
                               g);
          if (r == -1.0) {
            m.nodes[n].deadend = true;
          }
          cbackprop(m,n,r);
        }
        else {
          int n_p = cexpansion(m,n,domain,g);
          auto r = csimulation(hzn,
                               m.nodes[n_p].state, 
                               m.nodes[n_p].tasks, 
                               domain,
                               g);
          if (r == -1.0) {
            m.nodes[n_p].deadend = true;
          }
          cbackprop(m,n_p,r);
        }
      }
    }
    if (m.nodes[w].successors.empty()) {
      continue;
    }
    std::vector<int> arg_maxes = {};
    double max = -std::numeric_limits<double>::infinity();
    for (auto const &s : m.nodes[w].successors) {
      if (!m.nodes[s].deadend) {
        double mean = m.nodes[s].mean;
        if (mean >= max) {
          if (mean > max) {
            max = mean;
            arg_maxes.clear();
            arg_maxes.push_back(s);
          }
          else {
            arg_maxes.push_back(s); 
          }
        }
      }
    }
    if (arg_maxes.empty() || max == -1.0) {
      continue;
    }
    int arg_max = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.state = m.nodes[arg_max].state;
    k.tasks = m.nodes[arg_max].tasks;
    k.plan = m.nodes[arg_max].plan;

    k.depth = t.nodes[v].depth + 1;
    k.pred = v;
    int y = t.add_node(k);
    t.nodes[v].successors.push_back(y);
    v = y;
    if (t.nodes[v].plan.size() >= plan_size && plan_size != -1) {
      break;
    }
      
    bool plan_break = false;
    while (m.nodes[arg_max].successors.size() == 1) {
      if (m.nodes[arg_max].deadend) {
        continue;
      }
      arg_max = m.nodes[arg_max].successors.front();

      pNode j;
      j.state = m.nodes[arg_max].state;
      j.tasks = m.nodes[arg_max].tasks;
      j.plan = m.nodes[arg_max].plan;
      j.depth = t.nodes[v].depth + 1;
      j.pred = v;
      int y = t.add_node(j);
      t.nodes[v].successors.push_back(y);
      v = y;

      if (t.nodes[v].plan.size() >= plan_size && plan_size != -1) {
        plan_break = true;
        break;
      }
    }
    if (plan_break) {
      break;
    }
  }
  std::cout << "Plan found at depth " << t.nodes[v].depth;
  std::cout << std::endl;
  std::cout << "Final State:" << std::endl;
  t.nodes[v].state.print_facts();
  std::cout << std::endl;
  return v;

}

std::pair<pTree,std::pair<int,int>> 
cppMCTShop(DomainDef& domain,
           ProblemDef& problem,
           Scorer scorer,
           int R = 30,
           int plan_size = -1,
           double eps = 0.4,
           int successes = 19,
           double prob = 0.75,
           int seed = 4021) {
    domain.set_scorer(scorer);
    pTree t;
    pNode root;
    root.state = KnowledgeBase(domain.predicates,problem.objects,domain.typetree);
    for (auto const& f : problem.initF) {
      root.state.tell(f,false,false);
    }
    root.state.update_state();
    Grounded_Task init_t;
    init_t.first = problem.head;
    init_t.second = {};
    root.tasks.push_back(init_t);
    root.plan = {};
    root.depth = 0;
    int v = t.add_node(root);
    static std::mt19937_64 g(seed);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    t.nodes[v].state.print_facts();
    std::cout << std::endl;
    auto end = cseek_planMCTS(t, v, domain, R, plan_size, eps, successes,prob,g);
    std::cout << "Plan:";
    for (auto const& p : t.nodes[end].plan) {
      std::cout << " " << p;
    }
    std::cout << std::endl;
    return std::make_pair(t,std::make_pair(v,end));
}
