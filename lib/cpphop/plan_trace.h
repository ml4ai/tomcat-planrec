#pragma once
#include <nlohmann/json.hpp>
#include "Tree.h"
#include "Node.h"
#include "util.h"
#include <iomanip>
#include <iostream>
#include <fstream>
#include <string>

using json = nlohmann::ordered_json;

struct json_node {
  json node;
  int id;
};

//All of these are specifically made for MCTS algorithm
template<class State, class Selector> 
json_node gptt(Tree<State,Selector> t, int v) {
  json j;
  
  if (t[v].successors.empty()) {
    json_node n;
    n.node = j;
    n.id = -1;
    return n;
  }

  j["task"] = task2string(t[v].tasks.back());
  j["likelihood"] = t[v].likelihood;
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

template<class State, class Selector>
json generate_plan_trace_tree(Tree<State,Selector> t, int v, bool gen_file = false, std::string outfile = "plan_trace_tree.json") {
  auto g = gptt(t,v);
  g.node["Final State"] = t[g.id].state.to_json();
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << g.node << std::endl;
  }
  return g.node;
}

template<class State, class Selector>
json gpt(Tree<State,Selector> t, int v, json j) {
  int w = t[v].successors.back();
  if (t[w].tasks.size() < t[v].tasks.size()) {
    json g;
    g["task"] = task2string(t[v].tasks.back());
    g["pre-state"] = t[v].state.to_json();
    g["post-state"] = t[w].state.to_json();
    j.push_back(g);
  }

  if (t[w].successors.empty()) {
    json g;
    g["Final State"] = t[w].state.to_json();
    j.push_back(g);
    return j;
  }

  return gpt(t,w,j); 

}

template<class State, class Selector>
json generate_plan_trace(Tree<State,Selector> t, int v, bool gen_file = false, std::string outfile = "plan_trace.json") {
  json j;
  auto g = gpt(t,v,j);
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << g << std::endl;
  }
  return g;
}

json_node t_a(json g, json j, int acts) {
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
    json g_c;
    auto p = t_a(g_c,element,acts);
    g["children"].push_back(p.node);
    acts = p.id;
  }
  json_node n;
  n.node = g;
  n.id = acts;
  return n;
}

json trim_actions(json j, int acts, bool gen_file = false, std::string outfile = "trimmed_tree.json") {
  json g;
  auto t = t_a(g,j,acts);
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << t.node << std::endl;
  }
  return t.node;
}
