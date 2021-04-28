#pragma once

#include <iostream>
#include <map>
#include "cpphop.h"
#include "util.h"

template <class State>
class Node {
  public:
    State state;
    Tasks tasks;
    int depth;
    bTasks plan;
};
