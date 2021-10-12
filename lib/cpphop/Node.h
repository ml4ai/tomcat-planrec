#pragma once

#include <nlohmann/json.hpp>
#include <iostream>
#include <map>
#include <math.h>
#include "typedefs.h"

using json = nlohmann::json;

template <class State,class Selector>
struct Node {
    State state;
    Tasks tasks;
    int depth;
    pTasks plan;
    cTasks cplan;
    CFM cfm;
    json team_plan;
    Selector selector;
    double likelihood;

    //See Tree.hpp note for why these are needed
    int pred = -1;
    std::vector<int> successors = {};

};
