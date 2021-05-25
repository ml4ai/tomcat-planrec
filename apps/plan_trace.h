#pragma once
#include <nlohmann/json.hpp>
#include "Tree.h"
#include "Node.h"
#include "util.h"
#include <iomanip>
#include <iostream>
#include <fstream>

using json = nlohmann::ordered_json;

//All of these are specifically made for MCTS algorithm
template<class State, class Selector> 
std::pair<json,int> gptt(Tree<State,Selector> t, int v) {
  json j;

  j["task"] = task2string(t[v].tasks.back());
  j["log_likelihood"] = t[v].log_likelihood;
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
   j["children"].push_back(temp.first);
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
    g["log_likelihood"] = t[v].log_likelihood;
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
