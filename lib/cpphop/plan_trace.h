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

//All of these are specifically made for MCTS algorithm
template<class State, class Selector> 
std::pair<json,int> gptt(Tree<State,Selector> t, int v) {
  json j;
  
  if (t[v].successors.empty()) {
    return std::make_pair(j,-1);
  }

  j["task"] = task2string(t[v].tasks.back());
  j["likelihood"] = t[v].likelihood;
  j["pre-state"] = t[v].state.to_json();
  
  int w = t[v].successors.back();

  if (t[w].tasks.size() < t[v].tasks.size()) {
    j["post-state"] = t[w].state.to_json();
    j["children"] = R"([])"_json;
    return std::make_pair(j,w); 
  }
  int r = (t[w].tasks.size() - t[v].tasks.size()) + 1;
  for (int i = 0; i < r; i++) {
    std::pair temp = gptt(t,w);
    if (temp.second == -1) {
      break;
    }
    if ((i == r - 1) && (temp.first["task"] == j["task"])) {
      j["children"].insert(j["children"].end(),temp.first["children"].begin(),temp.first["children"].end());  
    }
    else {
      j["children"].push_back(temp.first);
    }
    w = temp.second;
  }
  return std::make_pair(j,w);
}

template<class State, class Selector>
json generate_plan_trace_tree(Tree<State,Selector> t, int v, bool gen_file = false, std::string outfile = "plan_trace_tree.json") {
  auto g = gptt(t,v);
  g.first["Final State"] = t[g.second].state.to_json();
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << g.first << std::endl;
  }
  return g.first;
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

std::pair<json,int> t_a(json g, json j, int acts) {
  g["task"] = j["task"];
  g["pre-state"] = j["pre-state"];
  g["post_state"] = j["post-state"];
  std::string tmp = g["task"].get<std::string>();
  if (tmp[1] == '!') {
    acts--;
    return std::make_pair(g,acts);
  }

  for (auto& element : j["children"]) {
    if (acts == 0) {
      break;
    }
    json g_c;
    std::pair<json,int> p = t_a(g_c,element,acts);
    g["children"].push_back(p.first);
    acts = p.second;
  }
  return std::make_pair(g,acts);
}

json trim_actions(json j, int acts, bool gen_file = false, std::string outfile = "trimmed_tree.json") {
  json g;
  auto t = t_a(g,j,acts);
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << t.first << std::endl;
  }
  return t.first;

}
