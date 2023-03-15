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
#include "cppMCTShop.h"
#include "Redis_Connect.h"
#include <boost/json.hpp>

namespace json = boost::json;

bool is_subseq(std::vector<std::string> plan, std::vector<std::pair<int,std::string>> O) {
  for (int i = 0; i < plan.size(); i++) {
    if (plan[i].find(O[i].second) == std::string::npos) {
      return false;
    }
  }
  return true;
}

void update_actions(std::string const& redis_address, 
                    std::vector<std::pair<int, std::string>>& actions) {
  Redis_Connect* rc = Redis_Connect::getInstance(redis_address);
  std::string oldest;
  if (actions.empty()) {
    oldest = "0";
  }
  else {
    oldest = std::to_string(actions.back().first);
  }
  std::vector<std::pair<std::string,std::pair<std::string,std::string>>> xresults;
  rc->redis.xread("actions",oldest,std::chrono::milliseconds(15000),1,std::back_inserter(xresults));
  if (xresults.empty()) {
    std::pair<int,std::string> p;
    p.first = -1;
    p.second = "__STOP__";
    actions.push_back(p);
  }
  for (auto const& x : xresults) {
    std::pair<int,std::string> p;
    p.first = std::stoi(x.first);
    p.second = x.second.second;
    actions.push_back(p);
  }
}

void upload_plan_explanation(std::string const& redis_address, 
                             TaskTree& tasktree, 
                             std::vector<std::string>& plan) {
  //Serialize task tree and current plan
  json::object obj;
  obj["tasktree"] = json::value_from(tasktree);
  obj["plan"] = json::value_from(plan);
  std::string s = json::serialize(obj);
  std::string rank = std::to_string(plan.size()) + "-*";
  Redis_Connect* rc = Redis_Connect::getInstance(redis_address);
  rc->redis.xadd("explanations",rank,{std::make_pair("explanation",s)});
}

double
simulation_rec(std::vector<std::pair<int,std::string>>& actions,
               std::vector<std::string> plan,
               KnowledgeBase state,
               TaskGraph tasks,
               int cTask,
               DomainDef& domain,
               Reach_Map& r_map,
               std::mt19937_64& g) {

  if (!is_subseq(plan,actions)) {
    return -1.0;
  }

  if (plan.size() == actions.size() || (tasks.empty() && cTask == -1)) {
    return domain.score(state,plan);
  }


  if (cTask != -1) {
    if (domain.actions.contains(tasks[cTask].head)) {
      if (plan.size() < actions.size()) {
        if (actions[plan.size()].second.find(tasks[cTask].head) == std::string::npos) {
          return -1.0;
        }
      }
      auto act = domain.actions.at(tasks[cTask].head).apply(state,tasks[cTask].args);
      if (!act.second.empty()) {
        std::shuffle(act.second.begin(),act.second.end(),g);
        auto gtasks = tasks;
        gtasks.remove_node(cTask);
        for (auto &ns : act.second) {
          auto gplan = plan;
          gplan.push_back(act.first+"_"+std::to_string(cTask));
          if (gplan.size() < actions.size()) {
            ns.update_state(actions[gplan.size()].first);
          }
          else {
            ns.update_state();
          }
          double rs = simulation_rec(actions,gplan,ns,gtasks,-1,domain,r_map,g);
          if (rs > -1.0) {
            return rs;
          }
        }
      }
      else {
        return -1.0;
      }
    }
    else if (domain.methods.contains(tasks[cTask].head)) {
      auto task_methods = domain.methods[tasks[cTask].head];
      std::shuffle(task_methods.begin(),task_methods.end(),g);
      bool not_applicable = true;
      for (auto &m : task_methods) {
        bool can_reach = false;
        if (r_map.find(m.get_head()) != r_map.end() && plan.size() < actions.size()) {
          for (auto const& a : r_map[m.get_head()]) {
            if (actions[plan.size()].second.find(a) != std::string::npos) {
              can_reach = true;
            } 
          } 
        }
        else {
          can_reach = true;
        }
        if (can_reach) {
          auto all_gts = m.apply(state,tasks[cTask].args,tasks,cTask);
          if (!all_gts.empty()) {
            not_applicable = false;
            std::shuffle(all_gts.begin(),all_gts.end(),g);
            for (auto &gts : all_gts) {
              double rs = simulation_rec(actions,plan,state,gts.second,-1,domain,r_map,g);
              if (rs > -1.0) {
                return rs;
              }
            }
          }
        }
      }
      if (not_applicable) {
        return -1.0;
      }
    }
    else {
      std::string message = "Invalid task ";
      message += tasks[cTask].head;
      message += " during simulation!";
      throw std::logic_error(message);
    }
  }
  else {
    for (auto &[i,gt] : tasks.GTs) {
      if (gt.incoming.empty()) {
        bool can_reach = false;
        if (r_map.find(gt.head) != r_map.end() && plan.size() < actions.size()) {
          for (auto const& a : r_map[gt.head]) {
            if (actions[plan.size()].second.find(a) != std::string::npos) {
              can_reach = true;
            }
          }
        }
        else {
          can_reach = true;
        }
        if (can_reach) {
          double rs = simulation_rec(actions,plan,state,tasks,i,domain,r_map,g);
          if (rs > -1.0) {
            return rs;
          }
        }
      }
    }
  }
  return -1.0;
}

int expansion_rec(std::vector<std::pair<int,std::string>> actions,
                  pTree& t,
                  int n,
                  DomainDef& domain,
                  Reach_Map r_map,
                  std::mt19937_64& g) {
    if (t[n].cTask != -1) {
      int tid = t[n].cTask;
      if (domain.actions.contains(t[n].tasks[tid].head)) {
        if (t[n].plan.size() < actions.size()) {
          if (actions[t[n].plan.size()].second.find(t[n].tasks[tid].head) == std::string::npos) {
            return n;
          }
        }
        auto act = domain.actions.at(t[n].tasks[tid].head).apply(t[n].state,t[n].tasks[tid].args);
        if (!act.second.empty()) {
          std::vector<int> a;
          for (auto const& state : act.second) {
            pNode v;
            v.state = state;
            v.tasks = t[n].tasks;
            v.tasks.remove_node(tid);
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.plan.push_back(act.first+"_"+std::to_string(tid));
            if (v.plan.size() < actions.size()) {
              v.state.update_state(actions[v.plan.size()].first);
            }
            else {
              v.state.update_state();
            }
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
          bool can_reach = false;
          if (r_map.find(m.get_head()) != r_map.end() && t[n].plan.size() < actions.size()) {
            for (auto const& a : r_map[m.get_head()]) {
              if (actions[t[n].plan.size()].second.find(a) != std::string::npos) {
                can_reach = true;
              }
            }
          }
          else {
            can_reach = true;
          }
          if (can_reach) {
            auto gts = m.apply(t[n].state,t[n].tasks[tid].args,t[n].tasks,tid);
            for (auto &g : gts) {
              pNode v;
              v.state = t[n].state;
              v.tasks = g.second;
              v.depth = t[n].depth + 1;
              v.plan = t[n].plan;
              v.addedTIDs = g.first;
              v.prevTID = tid;
              v.pred = n;
              int w = t.size();
              t[w] = v;
              t[n].successors.push_back(w);
              choices.push_back(w);
            }
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
    else {
      std::vector<int> gts;
      for (auto const& [id,gt] : t[n].tasks.GTs) {
        if (gt.incoming.empty()) {
          bool can_reach = false;
          if (r_map.find(gt.head) != r_map.end() && t[n].plan.size() < actions.size()) {
            for (auto const& a : r_map[gt.head]) {
              if (actions[t[n].plan.size()].second.find(a) != std::string::npos) {
                can_reach = true;
              }
            }
          }
          else {
            can_reach = true;
          }
          if (can_reach) {
            pNode v;
            v.cTask = id;
            v.state = t[n].state;
            v.tasks = t[n].tasks;
            v.depth = t[n].depth + 1;
            v.plan = t[n].plan;
            v.pred = n;
            int w = t.size();
            t[w] = v;
            t[n].successors.push_back(w);
            gts.push_back(w);
          }
        }
      }
      if (!gts.empty()) {
        int r = *select_randomly(gts.begin(), gts.end(), g);
        return r;
      }
      else {
        t[n].deadend = true;
        return n;
      }
    }
    t[n].deadend = true;
    return n;
}

bool
seek_planrecMCTS(pTree& t,
                 TaskTree& tasktree,
                 int v,
                 DomainDef& domain,
                 Reach_Map& r_map,
                 int R,
                 double c,
                 std::mt19937_64& g,
                 std::vector<std::pair<int,std::string>>& actions,
                 std::string const& redis_address) {
  int stuck_counter = 1000;
  t[v].time = actions.back().first;
  while (!t[v].tasks.empty()) {
    pTree m;
    pNode n_node;
    n_node.cTask = t[v].cTask;
    t[v].state.update_temporal_facts(redis_address);
    t[v].state.update_state(t[v].time);
    n_node.state = t[v].state;
    n_node.tasks = t[v].tasks;
    n_node.depth = t[v].depth;
    n_node.plan = t[v].plan;
    int w = m.size();
    m[w] = n_node;
    for (int i = 0; i < R; i++) {
      int n = selection(m,w,c,g);
      if (w == n && m[n].deadend) {
        std::cout << "Deadend, attempting to restart plan recognition process" << std::endl;
        return false;  
      }
      if (m[n].sims == 0) {
        m[n].state.update_state(m[n].time);
        double r = simulation_rec(actions,
                                  m[n].plan,
                                  m[n].state, 
                                  m[n].tasks, 
                                  m[n].cTask,
                                  domain,
                                  r_map,
                                  g);
    
        if (r == -1.0) {
          m[n].deadend = true;
          backprop(m,n,0);
        }
        else {
          backprop(m,n,r);
        }
      }
      else {
        m[n].state.update_state(m[n].time);
        int n_p = expansion_rec(actions,m,n,domain,r_map,g);
        double r = simulation_rec(actions,
                                  m[n_p].plan,
                                  m[n_p].state, 
                                  m[n_p].tasks, 
                                  m[n_p].cTask,
                                  domain,
                                  r_map,
                                  g);
        if (r == -1.0) {
          m[n_p].deadend = true;
          backprop(m,n_p,0);
        }
        else {
          backprop(m,n_p,r);
        }
      }
    }
    if (m[w].successors.empty()) {
      stuck_counter--;
      if (stuck_counter <= 0) {
        throw std::logic_error("Plan recognition is stuck, terminating process!");
      }
      continue;
    }

    std::vector<int> arg_maxes = {};
    double max = -std::numeric_limits<double>::infinity();
    for (auto const &s : m[w].successors) {
      if (!m[s].deadend) {
        double mean = m[s].score/m[s].sims;
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
    if (arg_maxes.empty() || max <= 0) {
      stuck_counter--;
      if (stuck_counter <= 0) {
        throw std::logic_error("Plan recognition is stuck, terminating process!");
      }
      continue;
    }
    stuck_counter = 1000;
    int arg_max = *select_randomly(arg_maxes.begin(), arg_maxes.end(), g); 
    pNode k;
    k.cTask = m[arg_max].cTask;
    k.state = m[arg_max].state;
    k.tasks = m[arg_max].tasks;
    k.plan = m[arg_max].plan;
    k.depth = t[v].depth + 1;
    for (auto& i : m[arg_max].addedTIDs) {
      TaskNode tasknode;
      tasknode.task = k.tasks[i].head;
      tasknode.token = k.tasks[i].to_string();
      tasknode.outgoing = k.tasks[i].outgoing;
      tasktree[i] = tasknode;
      tasktree[m[arg_max].prevTID].children.push_back(i);
    }
    k.pred = v;
    int y = t.size();
    t[y] = k;
    t[v].successors.push_back(y);
    v = y;
    if (actions.size() == t[v].plan.size()) {
      upload_plan_explanation(redis_address,tasktree,t[v].plan);
      update_actions(redis_address,actions);
      if (actions.back().second == "__STOP__") {
        std::cout << "No more incoming actions, stopping plan recognition process" << std::endl;
        return true;
      }
      t[v].time = actions.back().first;
    }

    while (m[arg_max].successors.size() == 1) {
      if (m[arg_max].deadend) {
        return false;
      }
      arg_max = m[arg_max].successors.front();
      pNode j;
      j.cTask = m[arg_max].cTask;
      j.state = m[arg_max].state;
      j.tasks = m[arg_max].tasks;
      j.plan = m[arg_max].plan;
      j.depth = t[v].depth + 1;
      for (auto& i : m[arg_max].addedTIDs) {
        TaskNode tasknode;
        tasknode.task = j.tasks[i].head;
        tasknode.token = j.tasks[i].to_string();
        tasknode.outgoing = j.tasks[i].outgoing;
        tasktree[i] = tasknode;
        tasktree[m[arg_max].prevTID].children.push_back(i);
      }
      j.pred = v;
      int y = t.size();
      t[y] = j;
      t[v].successors.push_back(y);
      v = y;
      if (actions.size() == t[v].plan.size()) {
        upload_plan_explanation(redis_address,tasktree,t[v].plan);
        update_actions(redis_address,actions);
        if (actions.back().second == "__STOP__") {
          std::cout << "No more incoming actions, stopping plan recognition process" << std::endl;
          return true;
        }
        t[v].time = actions.back().first;
      }
    }
  }
  std::cout << "No more tasks to decompose, stopping plan recognition process" << std::endl;
  return true;
}

void 
cppMCTSplanrec(DomainDef& domain,
              ProblemDef& problem,
              Reach_Map& r_map,
              Scorer scorer,
              int R = 30,
              double c = 1.4,
              int seed = 4021,
              std::string const& redis_address = "") {
    if (redis_address.empty()) {
      std::cout << "Redis Database address not given, ending plan recognition process" << std::endl;
      return;
    }
    bool end = false;
    std::vector<std::pair<int,std::string>> actions;
    while(!end) {
      domain.set_scorer(scorer);
      pTree t;
      TaskTree tasktree;
      pNode root;
      root.state = KnowledgeBase(domain.predicates,problem.objects,domain.typetree);
      for (auto const& f : problem.initF) {
        root.state.tell(f,false,false);
      }
      root.state.update_state();
      Grounded_Task init_t;
      init_t.head = problem.head;
      int TID = root.tasks.add_node(init_t);
      TaskNode tasknode;
      tasknode.task = init_t.head;
      tasknode.token = init_t.to_string();
      tasktree[TID] = tasknode;
      root.plan = {};
      root.depth = 0;
      int v = t.size();
      t[v] = root;
      static std::mt19937_64 g(seed);
      seed++;
      update_actions(redis_address,actions);
      if (actions.back().second == "__STOP__") {
        std::cout << "No more incoming actions, stopping plan recognition process" << std::endl;
        return;
      }
      end = seek_planrecMCTS(t, 
                             tasktree, 
                             v, 
                             domain, 
                             r_map,
                             R, 
                             c, 
                             g,
                             actions,
                             redis_address);
    }
    return;
}
