# tomcat-planrec
Code for the plan recognition and planning effort in ToMCAT.

# Table of Contents
1. [Build Requirements](#build-requirements) 
2. [Installation](#installation) 
3. [MCTS HTN Planner](#mcts-htn-planner-and-mcts-hybrid-planner)

# Build Requirements
- cmake (Minimum requirement is version 3.16, https://cmake.org/)
- Boost (Minimum requirement is version 1.79, https://www.boost.org/)
  - Specific Boost Libraries to build: filesystem, log, date\_time, chrono, program\_options, coroutine, json
- Z3 (Minimum requirement is version 4.8.17, specifically the libraries for c++, https://github.com/Z3Prover/z3)
- Graphviz (Tested on version 8.0.5, https://graphviz.org/)
- OpenSLL (Tested on version 3.1.1, https://www.openssl.org/) 
- Paho MQTT (Tested on version 1.3.9)
- Hiredis (Tested on version 0.14.1, https://redis.io/lp/hiredis/)
- Redis-Plus-Plus (Tested on version 1.3.5, https://github.com/sewenew/redis-plus-plus)
- Tested on Apple clang version 15.0.0.15000309 (It may also work using GNU 11.4.0)
- Redis (This refers to actual client and server software, different than
  the required C and C++ libraries. Only the machine hosting the redis
  database, needs this. Tested on version 7.0.10)

# Installation

To build, do the following:

    mkdir -p build
    cd build
    cmake ..
    make -j

After building, you can run tests with the following command (assuming you are
in the `build` directory).

    ctest

If you want more verbose output (e.g. if you want to show the outputs from your
`cout << ... << endl` statements), run:

    ctest -V

# MCTS HTN Planner and MCTS Hybrid Planner

After building, you can run: 
    
    ./apps/planners/MCTS_planner

This will run the planner on default settings, which are the same as
test\_MCTS\_planner ran by the ctest command. 

The default domain and problem definitions are at domains/transport\_domain.hddl 
and domains/transport\_problem.hddl. The default score function is "delivery\_one" defined 
in domains/score\_functions.h. 

Run with the help flag,

    ./apps/planners/MCTS_planner -h

To see what options are available including how to run the planner with
different domain and problem definitions and score functions. Score functions
must be predefined in domains/score\_functions.h. 

## Running the MCTS HTN Plan Recognizer
After building, you can run: 
    
    ./apps/planrec/MCTS_planrec -g

This will run the planner on default settings. The `-g` flag has the plan
recognizer generate a png file containing a visual of the inferred plan
structure. By default the file name will be `__<problem_head>__.png`.  

The default domain and problem definitions are at domains/transport\_domain.hddl 
and domains/transport\_problem.hddl. The default score function is "delivery\_one" defined 
in domains/score\_functions.h. The default observation set is "delivery\_sample" with a sample size of 2 (i.e., the first two actions). 

Run with the help flag,

    ./apps/planrec/MCTS_planrec -h

To see what options are available including how to run the plan recognizer with
different domain and problem definitions and score functions. Score functions
must be predefined in domains/score\_functions.h. The script
domains/pr\_samples.h provides a convenient way to provide artificial
observation sets.   

# Acknowledgments

The C++ implementation of the
[PyHOP](https://bitbucket.org/dananau/pyhop/src/master/) planning algorithm
borrows from
[PCfVW/Simple-HTN-Planner](https://github.com/PCfVW/Simple-HTN-Planner).
