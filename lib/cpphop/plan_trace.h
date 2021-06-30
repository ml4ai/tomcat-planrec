#pragma once
#include <nlohmann/json.hpp>
#include "Tree.h"
#include "Node.h"
#include "../util.h"
#include <iomanip>
#include <iostream>
#include <fstream>

struct json_node {
  json node;
  int id;
};

//All of these are specifically made for MCTS algorithm
template<class State, class Selector> 
json_node gptt(Tree<State,Selector> t, int v) {
  json j;

  j["task"] = task2string(t[v].tasks.back());
  j["state"] = t[v].state.to_json();

  int w = t[v].successors.back();

  if (t[w].tasks.size() < t[v].tasks.size()) {
    j["children"] = R"([])"_json;
    json_node n;
    n.node = j;
    n.id = w;
    return n; 
  }
  int r = (t[w].tasks.size() - t[v].tasks.size()) + 1;
  for (int i = 0; i < r; i++) {
   auto temp = gptt(t,w);
   j["children"].push_back(temp.node);
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
    g["state"] = t[v].state.to_json();
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
