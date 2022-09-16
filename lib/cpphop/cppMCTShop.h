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
    TaskGraph tasks;
    std::vector<std::string> plan;
    int depth = 0;
    double mean = 0.0;
    int sims = 0;
    int pred = -1;
    bool deadend = false;
    std::vector<int> successors = {};
};

using pTree = std::unordered_map<int,pNode>;

int
cselection(pTree& t,
          int v,
          double eps,
          std::mt19937_64& g) {

    std::uniform_real_distribution<> dis(0.0,1.0);
    int original = v;
    while (!t[v].successors.empty()) {
      if (t[v].deadend) {
        return v;
      }
      double e = dis(g);
      if (e > eps) {
        std::vector<int> r_maxes = {};
        double r_max = -std::numeric_limits<double>::infinity();
        for (auto const &w : t[v].successors) {
          if (!t[w].deadend) {
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
        }
        if (r_maxes.empty()) {
          t[v].deadend = true;
          v = original;
          continue;
        }
        std::vector<int> v_maxes = {};
        v_maxes.push_back(r_maxes.front());
        int v_max = t[v_maxes.back()].sims;
        for (auto const &w : r_maxes) {
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
        v = *select_randomly(v_maxes.begin(), v_maxes.end(), g);
      }
      else {
        bool all_deadends = true;
        for (auto const &w : t[v].successors) {
          if (!t[w].deadend) {
            if (t[w].sims == 0) {
              return w;
            }
            all_deadends = false;
          }
        }
        if (all_deadends) {
          t[v].deadend = true;
          v = original;
          continue;
        }
        v = *select_randomly(t[v].successors.begin(), t[v].successors.end(), g);
      }
    }
    return v;
}

void cbackprop(pTree& t, int n, double r) {
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

double
csimulation(int horizon,
           KnowledgeBase state,
           TaskGraph tasks,
           DomainDef& domain,
           std::mt19937_64& g,
           int h = 0) {
  if (tasks.empty() || h >= horizon) {
    return domain.score(state);
  }
  h++;
  for (auto &[i,gt] : tasks.GTs) {
    if (gt.incoming.empty()) {
      if (domain.actions.contains(gt.head)) {
        auto act = domain.actions.at(gt.head).apply(state,gt.args);
        if (!act.second.empty()) {
          std::shuffle(act.second.begin(),act.second.end(),g);
          auto gtasks = tasks;
          gtasks.remove_node(i);
          for (auto &ns : act.second) {
            ns.update_state();
            double rs = csimulation(horizon,ns,gtasks,domain,g,h);
            if (rs > -1.0) {
              return rs;
            }
          }
        }
        else {
          return -1.0;
        }
      }
      else if (domain.methods.contains(gt.head)) {
        auto task_methods = domain.methods[gt.head];
        std::shuffle(task_methods.begin(),task_methods.end(),g);
        for (auto &m : task_methods) {
          auto all_gts = m.apply(state,gt.args,tasks,i);
          if (!all_gts.second.empty()) {
            std::shuffle(all_gts.second.begin(),all_gts.second.end(),g);
            for (auto &gts : all_gts.second) {
              double rs = csimulation(horizon,state,gts,domain,g,h);
              if (rs > -1.0) {
                return rs;
              }
            }
          }
          else {
            return -1.0;
          }
        }
      }
      else {
        std::string message = "Invalid task ";
        message += gt.head;
        message += " during simulation!";
        throw std::logic_error(message);
      }
    }
  }
  return -1.0;
}

int cexpansion(pTree& t,
              int n,
              DomainDef& domain,
              std::mt19937_64& g) {
    std::vector<int> gts; 
    for (auto const& [id,gt] : t[n].tasks.GTs) {
      if (gt.incoming.empty()) {
        gts.push_back(id);
      }
    }
    int tid = *select_randomly(gts.begin(), gts.end(), g); 
    if (domain.actions.contains(t[n].tasks[tid].head)) {
      auto act = domain.actions.at(t[n].tasks[tid].head).apply(t[n].state,t[n].tasks[tid].args);
      if (!act.second.empty()) {
        std::vector<int> a;
        for (auto const& state : act.second) {
          pNode v;
          v.state = state;
          v.state.update_state();
          v.tasks = t[n].tasks;
          v.tasks.remove_node(tid);
          v.depth = t[n].depth + 1;
          v.plan = t[n].plan;
          v.plan.push_back(act.first);
          v.pred = n;
          int w = t.size();
          t[w] = v;
          t[n].successors.push_back(w);
          a.push_back(w);
        }
        int r = *select_randomly(a.begin(), a.end(), g);
        return r;
      }
      t[n].deadend = true;
      return n;
    }

    if (domain.methods.contains(t[n].tasks[tid].head)) {
      std::vector<int> choices;
      for (auto &m : domain.methods[t[n].tasks[tid].head]) {
        auto gts = m.apply(t[n].state,t[n].tasks[tid].args,t[n].tasks,tid);
        for (auto &g : gts.second) { 
          pNode v;
          v.state = t[n].state;
          v.tasks = g;
          v.depth = t[n].depth + 1;
          v.plan = t[n].plan;
          v.pred = n;
          int w = t.size();
          t[w] = v;
          t[n].successors.push_back(w);
          choices.push_back(w);
        }
      }
      if (choices.empty()) {
        t[n].deadend = true;
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
  while (!t[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    int w = m.size();
    m[w] = n_node;
    int hzn = nbd(g);
    for (int i = 0; i < R; i++) {
      int n = cselection(m,w,eps,g);
      if (m[n].tasks.empty()) {
          cbackprop(m,n,domain.score(m[n].state));
      }
      else {
        if (m[n].sims == 0) {
          auto r = csimulation(hzn,
                               m[n].state, 
                               m[n].tasks, 
                               domain,
                               g);
          if (r == -1.0) {
            m[n].deadend = true;
          }
          cbackprop(m,n,r);
        }
        else {
          int n_p = cexpansion(m,n,domain,g);
          auto r = csimulation(hzn,
                               m[n_p].state, 
                               m[n_p].tasks, 
                               domain,
                               g);
          if (r == -1.0) {
            m[n_p].deadend = true;
          }
          cbackprop(m,n_p,r);
        }
      }
    }
    if (m[w].successors.empty()) {
      continue;
    }
    std::vector<int> arg_maxes = {};
    double max = -std::numeric_limits<double>::infinity();
    for (auto const &s : m[w].successors) {
      if (!m[s].deadend) {
        double mean = m[s].mean;
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
    k.state = m[arg_max].state;
    k.tasks = m[arg_max].tasks;
    k.plan = m[arg_max].plan;
    k.depth = t[v].depth + 1;
    k.pred = v;
    int y = t.size();
    t[y] = k;
    t[v].successors.push_back(y);
    v = y;
    if (t[v].plan.size() >= plan_size && plan_size != -1) {
      break;
    }
      
    bool plan_break = false;
    while (m[arg_max].successors.size() == 1) {
      if (m[arg_max].deadend) {
        continue;
      }
      arg_max = m[arg_max].successors.front();

      pNode j;
      j.state = m[arg_max].state;
      j.tasks = m[arg_max].tasks;
      j.plan = m[arg_max].plan;
      j.depth = t[v].depth + 1;
      j.pred = v;
      int y = t.size();
      t[y] = j;
      t[v].successors.push_back(y);
      v = y;

      if (t[v].plan.size() >= plan_size && plan_size != -1) {
        plan_break = true;
        break;
      }
    }
    if (plan_break) {
      break;
    }
  }
  std::cout << "Plan found at depth " << t[v].depth;
  std::cout << std::endl;
  std::cout << "Final State:" << std::endl;
  t[v].state.print_facts();
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
    init_t.head = problem.head;
    root.tasks.add_node(init_t);
    root.plan = {};
    root.depth = 0;
    int v = t.size();
    t[v] = root;
    static std::mt19937_64 g(seed);
    std::cout << std::endl;
    std::cout << "Initial State:" << std::endl;
    t[v].state.print_facts();
    std::cout << std::endl;
    auto end = cseek_planMCTS(t, v, domain, R, plan_size, eps, successes,prob,g);
    std::cout << "Plan:";
    for (auto const& p : t[end].plan) {
      std::cout << " " << p;
    }
    std::cout << std::endl;
    return std::make_pair(t,std::make_pair(v,end));
}
