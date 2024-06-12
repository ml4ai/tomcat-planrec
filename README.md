# tomcat-planrec
Code for the plan recognition and planning effort in ToMCAT.

# Table of Contents
1. [Build Requirements](#build-requirements) 
2. [Installation](#installation) 
3. [HDDL Domain and Problem Definition
   Loaders](#hddl-domain-and-problem-definition-loaders)
4. [MCTS Hierarchical Planners](#mcts-hierarchical-planners)
    1. [MCTS HTN Planner](#mcts-htn-planner) 
5. [MCTS Hierarchical Plan Recognizers](#mcts-hierarchical-plan-recognizers)

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

# HDDL Domain and Problem Definition Loaders
[Hierarchical Domain Definition Language
(HDDL)](https://staff.fnwi.uva.nl/g.behnke/papers/Hoeller2020HDDL.pdf) 
is a hierarchical extension to [Planning Domain Definition Language (PDDL)](https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language). 
It allows for a hierarchical planning problems to be defined in a 
standardized human-readable syntax. 

This code-base features a loading function for parsing HDDL and loading the
parsed elements into c++ data structures. These data structures can then be
used by our planner and plan recognition systems. See our [test\_loader](https://github.com/ml4ai/tomcat-planrec/blob/main/test/test_loader.cpp)
script for example usage.

## Current Capabilities
- Can fully parse and load all features of HDDL aside from the
  unsupported features listed below
- The "either" keyword is not currently supported
- Syntax and logic for the handling of external function calls are not
  currently supported
- Requirement checking for given requirement keys is not currently supported

# MCTS Hierarchical Planners
Our code-base features two types of [Monte Carlo Tree Search (MCTS)](https://en.wikipedia.org/wiki/Monte_Carlo_tree_search) 
Hierarchical Planners. Both types can use planning elements loaded from our HDDL domain and
problem definition loaders. We also supply a script for running the planners.
Its usage is detailed below. 

## MCTS HTN Planner
This planner uses a task decomposition method similar to
[SHOP2](https://arxiv.org/pdf/1106.4869) to generate grounded plans. However,
instead of using Depth-First Search, it runs a time-limited MCTS per each
planning decision in order to estimate the single best grounded plan according
to a user-defined score function. 

### Current Capabilities
- Can run domain and problem elements loaded from our HDDL domain and problem
  definition loaders
- Can handle ordering constraints on tasks, unconstrained tasks, and performs
  task interleaving
- We also developed a graphing function that can take the results of the
  planner and output a visual representation of the task hierarchy used to
  generate the grounded plan
- The problem definition requires a top-level task or set of partially-ordered top-level tasks
  from which to start the task decomposition process
- The task decomposition process is NOT goal directed and therefore it will
  ignore goal statements defined in problem definitions
- Shallow deadends and infinite recursive/looping tasks can cause
  the planner to "stall out"

### Running the Planner
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
must be predefined in domains/score\_functions.h. There are also options to run
the hybrid planner (discussed below).

## MCTS Hybrid Planner
Most of the internal mechanisms such as the use of time-limited MCTS are the
same for this planner as compared to the purely HTN version. This planner does
two-level planning and thus requires a secondary domain definition. It first does goal-driven 
classical planning to find a grounded partially-ordered set of compound tasks that satisfy a given
goal statement. These compound tasks must be defined in the secondary domain
definition as actions (i.e., to define state effects for them). Given a
solution from the classical planning phase, it then decomposes this set of
compound tasks into a grounded plan (given actions from the main domain
definition). 

### Current Capabilities
- It largely has the same capabilities as the HTN planner
- As state above, it requires a second auxiliary domain definition
- A goal statement is required in the problem definition
- The problem definition should omit any top-level tasks (this is what the
  classical planning phase accomplishes!)

### Running the Planner
After building, you can run same command show above for the HTN planner. You
will need to set an auxiliary domain using the `--aux_dom_file` (or `-x`) flag.
Likewise an approriate problem definition with the `:htn` key omitted and a
goal statement defined using the `:goal` key must be passed to the planner.
This can be using the `--prob_file` (or `-P`) flag. 
    
E.g.,

    ./apps/planners/MCTS_planner -x transport_domain_C.hddl -P transport_problem_C.hddl

# MCTS Hierarchical Plan Recognizer
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
