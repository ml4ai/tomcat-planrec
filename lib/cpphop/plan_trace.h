#pragma once

#include "../util.h"
#include <fstream>
#include "Node.h"
#include "Tree.h"
#include <iomanip>
#include <iostream>
#include "cppMCTShop.h"
#include "cppMCTSplanrec.h"
#include <nlohmann/json.hpp>

struct json_node {
    nlohmann::json node;
    int id;
};

//All of these are specifically made for MCTS algorithm
template<class State, class Selector> 
json_node gptt(Tree<State,Selector>& t, int v) {
  nlohmann::json j;
  
  if (t[v].successors.empty()) {
    json_node n;
    n.node = j;
    n.id = -1;
    return n;
  }

  j["task"] = task2string(t[v].tasks.back());
  j["pre-state"] = t[v].state.to_json();
  
  int w = t[v].successors.back();

  if (t[w].tasks.size() < t[v].tasks.size()) {
    j["post-state"] = t[w].state.to_json();
    j["children"] = R"([])"_json;
    json_node n;
    n.node = j;
    n.id = w;
    return n; 
  }
  int r = (t[w].tasks.size() - t[v].tasks.size()) + 1;
  for (int i = 0; i < r; i++) {
    auto temp = gptt(t,w);
    if (temp.id == -1) {
      break;
    }
    if ((i == r - 1) && (temp.node["task"] == j["task"])) {
      j["children"].insert(j["children"].end(),temp.node["children"].begin(),temp.node["children"].end());  
    }
    else {
      j["children"].push_back(temp.node);
    }
    w = temp.id;
  }
  json_node n;
  n.node = j;
  n.id = w;
  return n;
}

template <class State, class Selector>
nlohmann::json
generate_plan_trace_tree(Tree<State, Selector>& t,
                         int v,
                         bool gen_file = false,
                         std::string outfile = "plan_trace_tree.json") {
    auto g = gptt(t, v);
    g.node["Final State"] = t[g.id].state.to_json();
    if (gen_file) {
        std::ofstream o(outfile);
        o << std::setw(4) << g.node << std::endl;
    }
    return g.node;
}

template<class State, class Selector>
nlohmann::json gpt(Tree<State,Selector>& t, int v, nlohmann::json j) {
  int w = t[v].successors.back();
  if (t[w].tasks.size() < t[v].tasks.size()) {
    nlohmann::json g;
    Task task = t[v].tasks.back();
    if (task.task_id.find("!") != std::string::npos) {
      g["task"] = task2string(task);
      for (auto a : task.agents) {
        j["plan"][a].push_back(g);
        j["size"] = 1 + j["size"].get<int>();
      }
    }
  }

  if (t[w].successors.empty()) {
    return j;
  }

  return gpt(t, w, j);
}

template <class State, class Selector>
nlohmann::json generate_plan_trace(Tree<State, Selector>& t,
                                   int v,
                                   bool gen_file = false,
                                   std::string outfile = "plan_trace.json") {
    nlohmann::json j;
    j["size"] = 0;
    auto g = gpt(t, v, j);
    if (gen_file) {
        std::ofstream o(outfile);
        o << std::setw(4) << g << std::endl;
    }
    return g;
}

//For pTree and pNode
template<class State> 
json_node gptt(pTree<State>& t, int v) {
  nlohmann::json j;
  
  if (t.nodes[v].successors.empty()) {
    json_node n;
    n.node = j;
    n.id = -1;
    return n;
  }

  j["task"] = task2string(t.nodes[v].tasks.back());
  j["pre-state"] = t.nodes[v].state.to_json();
  
  int w = t.nodes[v].successors.back();

  if (t.nodes[w].tasks.size() < t.nodes[v].tasks.size()) {
    j["post-state"] = t.nodes[w].state.to_json();
    j["children"] = R"([])"_json;
    json_node n;
    n.node = j;
    n.id = w;
    return n; 
  }
  int r = (t.nodes[w].tasks.size() - t.nodes[v].tasks.size()) + 1;
  for (int i = 0; i < r; i++) {
    auto temp = gptt(t,w);
    if (temp.id == -1) {
      break;
    }
    if ((i == r - 1) && (temp.node["task"] == j["task"])) {
      j["children"].insert(j["children"].end(),temp.node["children"].begin(),temp.node["children"].end());  
    }
    else {
      j["children"].push_back(temp.node);
    }
    w = temp.id;
  }
  json_node n;
  n.node = j;
  n.id = w;
  return n;
}

template <class State>
nlohmann::json
generate_plan_trace_tree(pTree<State>& t,
                         int v,
                         bool gen_file = false,
                         std::string outfile = "plan_trace_tree.json") {
    auto g = gptt(t, v);
    g.node["Final State"] = t.nodes[g.id].state.to_json();
    if (gen_file) {
        std::ofstream o(outfile);
        o << std::setw(4) << g.node << std::endl;
    }
    return g.node;
}

template<class State>
nlohmann::json gpt(pTree<State>& t, int v, nlohmann::json j) {
  int w = t.nodes[v].successors.back();
  if (t.nodes[w].tasks.size() < t.nodes[v].tasks.size()) {
    nlohmann::json g;
    Task task = t.nodes[v].tasks.back();
    if (task.task_id.find("!") != std::string::npos) {
      g["task"] = task2string(task);
      for (auto a : task.agents) {
        j["plan"][a].push_back(g);
        j["size"] = 1 + j["size"].get<int>();
      }
    }
  }

  if (t.nodes[w].successors.empty()) {
    return j;
  }

  return gpt(t, w, j);
}

template <class State>
nlohmann::json generate_plan_trace(pTree<State>& t,
                                   int v,
                                   bool gen_file = false,
                                   std::string outfile = "plan_trace.json") {
    nlohmann::json j;
    j["size"] = 0;
    auto g = gpt(t, v, j);
    if (gen_file) {
        std::ofstream o(outfile);
        o << std::setw(4) << g << std::endl;
    }
    return g;
}

//For prTree and prNode
template<class State> 
json_node gptt(prTree<State>& t, int v) {
  nlohmann::json j;
  
  if (t.nodes[v].successors.empty()) {
    json_node n;
    n.node = j;
    n.id = -1;
    return n;
  }

  j["task"] = task2string(t.nodes[v].tasks.back());
  j["pre-state"] = t.nodes[v].state.to_json();
  
  int w = t.nodes[v].successors.back();

  if (t.nodes[w].tasks.size() < t.nodes[v].tasks.size()) {
    j["post-state"] = t.nodes[w].state.to_json();
    j["children"] = R"([])"_json;
    json_node n;
    n.node = j;
    n.id = w;
    return n; 
  }
  int r = (t.nodes[w].tasks.size() - t.nodes[v].tasks.size()) + 1;
  for (int i = 0; i < r; i++) {
    auto temp = gptt(t,w);
    if (temp.id == -1) {
      break;
    }
    if ((i == r - 1) && (temp.node["task"] == j["task"])) {
      j["children"].insert(j["children"].end(),temp.node["children"].begin(),temp.node["children"].end());  
    }
    else {
      j["children"].push_back(temp.node);
    }
    w = temp.id;
  }
  json_node n;
  n.node = j;
  n.id = w;
  return n;
}

template <class State>
nlohmann::json
generate_plan_trace_tree(prTree<State>& t,
                         int v,
                         bool gen_file = false,
                         std::string outfile = "plan_trace_tree.json") {
    auto g = gptt(t, v);
    g.node["Final State"] = t.nodes[g.id].state.to_json();
    if (gen_file) {
        std::ofstream o(outfile);
        o << std::setw(4) << g.node << std::endl;
    }
    return g.node;
}

template<class State>
nlohmann::json gpt(prTree<State>& t, int v, nlohmann::json j) {
  int w = t.nodes[v].successors.back();
  if (t.nodes[w].tasks.size() < t.nodes[v].tasks.size()) {
    nlohmann::json g;
    Task task = t.nodes[v].tasks.back();
    if (task.task_id.find("!") != std::string::npos) {
      g["task"] = task2string(task);
      for (auto a : task.agents) {
        j["plan"][a].push_back(g);
        j["size"] = 1 + j["size"].get<int>();
      }
    }
  }

  if (t.nodes[w].successors.empty()) {
    return j;
  }

  return gpt(t, w, j);
}

template <class State>
nlohmann::json generate_plan_trace(prTree<State>& t,
                                   int v,
                                   bool gen_file = false,
                                   std::string outfile = "plan_trace.json") {
    nlohmann::json j;
    j["size"] = 0;
    auto g = gpt(t, v, j);
    if (gen_file) {
        std::ofstream o(outfile);
        o << std::setw(4) << g << std::endl;
    }
    return g;
}

json_node t_a(nlohmann::json g, nlohmann::json j, int acts) {
  g["task"] = j["task"];
  g["pre-state"] = j["pre-state"];
  g["post_state"] = j["post-state"];
  std::string tmp = g["task"].get<std::string>();
  if (tmp[1] == '!') {
    acts--;
    json_node n;
    n.node = g;
    n.id = acts;
    return n;
  }

  for (auto& element : j["children"]) {
    if (acts == 0) {
      break;
    }
    nlohmann::json g_c;
    auto p = t_a(g_c,element,acts);
    g["children"].push_back(p.node);
    acts = p.id;
  }
  json_node n;
  n.node = g;
  n.id = acts;
  return n;
}

nlohmann::json trim_actions(nlohmann::json j, int acts, bool gen_file = false, std::string outfile = "trimmed_tree.json") {
  nlohmann::json g;
  auto t = t_a(g,j,acts);
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << t.node << std::endl;
  }
  return t.node;
}
