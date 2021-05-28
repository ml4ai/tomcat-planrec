#pragma once

#include <iostream>
#include <map>
#include "cpphop.h"
#include "util.h"
#include <math.h>
#include <nlohmann/json.hpp>

using json = nlohmann::ordered_json;

template <class State,class Selector>
class Node {
  public:
    State state;
    Tasks tasks;
    int depth;
    pTasks plan;
    json plan_trace;
    Selector selector;
    double log_likelihood;

    //See Tree.hpp note for why these are needed
    int pred = -1;
    std::vector<int> successors = {};

    friend bool operator== (Node<State,Selector> & lhs, Node<State,Selector> & rhs) {
      return (lhs.state == rhs.state && lhs.tasks == rhs.tasks && lhs.depth == rhs.depth && lhs.plan == rhs.plan);
    }
};
