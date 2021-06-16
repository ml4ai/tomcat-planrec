# HTN Planner and Plan Recognition
This code executes an HTN planner based off of SHOP and PYHOP, a Monte Carlo
Tree Search (MCTS) version of SHOP, and a MCTS plan recognition algorithm. 
It is written in C++.

# Requirements
- Boost (Tested on version 1.71.0, obtained from `sudo port install boost`)
- cmake (Tested on version 3.19.8, obtained from `sudo port install cmake`)
- Nhlohmann-json (Tested on version 3.9.1, obtained from `sudo port install
  nlohmann-json`)
- Graphviz (Tested on version 2.40.1, obtained from `sudo port install graphviz`)
- Tested with gcc compiler (version 9.3.0), but could possibly work with clang or other versions that support C++20. 

# Building planners and plan recognition algorithm
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

This will generate 2 json files, one is the plan tree and the other is
the plan trace. 

It also produces a plan tree graph in a png file. Generated plan tree graphs depict
compound tasks as oval nodes and black outline, and primitive tasks (i.e., actions) as
rectangular nodes and blue outlines. 

Allows to parameters to be taken from the command line. The
first parameter is the number of resource loops allowed (default at N = 30) and
the second is a exploration parameter (default at e = 0.4). For now, the loop
parameter must be set manually to set the exploration parameter. 

This script is currently set to have the agent utilize a yellow first triage strategy and to
explore the regions from right to left (sweep left).

EX:

    ./simple_sar_MCTS_planner 100 0.4

Note: The planner can run a little slow, it is recommended that you run this
very sparingly. You will only need to generate the json files from the planner once 
to run the plan recognition algorithm (discussed in the next section) any number of times. 

# Generate plan explanation for a given plan trace of the Simple SAR Domain

You must first generate a plan trace and a plan tree from the simple SAR domain to run the plan
recognition algorithm. This can be done using the MCTS planner script discussed
in the previous section. 

Once a plan trace has been generated, run:

    ./simple_sar_MCTS_planrec

This will generate 2 json files, where one is a partial plan tree predicting
the task hierarchy (i.e., the explanation) for the given plan trace and the
other is the true partial plan tree giving what the explanation should be. 
The explanation will start with the SAR task at it's root, whereas the true 
plan tree will just start with the chosen triage and navigation strategy task 
at its root (e.g., sweep_left_YF). 

This script also generates corresponding partial plan tree graphs of the predicted
and true plan explanations as png files. 

This script can take 2 command line arguments, the number of resource loops
allowed (default at N = 30) and the size of the trace (default at s = 5). The script itself reads a full plan trace,
but can use the trace size parameter to simulate having only a partial trace.
As with the MCTS planner, the loop parameter must be set manually to allow for
the trace size to be set. 

EX:

    ./simple_sar_MCTS_planrec 30 2

Note: Not allowing enough resource loops can cause odd behavior in the plan
recognition. Also keep in mind that the larger the trace size, the more loops
are needed for an accurate prediction.  
