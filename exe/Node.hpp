#pragma once

#include <iostream>
#include <map>
#include "cpphop.h"
#include "util.h"

template <class State,class Selector>
class Node {
  public:
    State state;
    Tasks tasks;
    int depth;
    bTasks plan;
    Selector selector;
    int pred = -1;
    std::vector<int> successors = {};

    friend bool operator== (Node<State,Selector> & lhs, Node<State,Selector> & rhs) {
      return (lhs.state == rhs.state && lhs.tasks == rhs.tasks && lhs.depth == rhs.depth && lhs.plan == rhs.plan);
    }
};
