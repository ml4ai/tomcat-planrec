#pragma once

#include <nlohmann/json.hpp>
#include <iostream>
#include <map>
#include "cpphop.h"
#include <math.h>
#include "typedefs.h"

using json = nlohmann::json;

template <class State,class Selector>
class Node {
  public:
    State state;
    Tasks tasks;
    int depth;
    pTasks plan;
    cTasks cplan;
    json team_plan;
    Selector selector;
    double likelihood;

    //See Tree.hpp note for why these are needed
    int pred = -1;
    std::vector<int> successors = {};

};
