# HTN Planner
This code executes an HTN planner based off of SHOP and PYHOP. It is written in
C++

# Requirements
- Boost (Tested on version 1.71.0, obtained from `sudo port install boost`)
- cmake (Tested on version 3.19.8, obtained from `sudo port install cmake`)
- Nhlohmann-json (Tested on version 3.9.1, obtained from `sudo port install
  nlohmann-json`) 
- Tested with gcc compiler (version 9.3.0), but could possibly work with clang or other versions that support C++20. 

# Building planner
To build:

    mkdir build
    cd build
    cmake ..
    make -j

# Generate plans for Simple Travel Domain (DFS Algorithm)

To run:

    ./simple_travel_planner

# Generate plans for Simple SAR Domain (DFS Algorithm)

To run:

  ./simple_sar_planner

WARNING: This is a brute force algorithm that attempts to generate all possible plans and 
would most likely take several hours or days to complete.  

# Generate plans and plan traces for Simple SAR Domain (MCTS Algorithm)

To run:

  ./simple_sar_MCTS_planner

This will generate 2 json files, one is the plan trace tree and the other is
the plan trace.
