# tomcat-planrec

# Requirements
- cmake (Minimum requirement is 3.16, https://cmake.org/)
- Boost (Minimum requirement is 1.79, https://www.boost.org/)
  - Specific Boost Libraries to build: filesystem, log, date\_time, chrono, program\_options, coroutine, json
- Z3 (Minimum requirement is 4.8.17, specifically the libraries for c++, https://github.com/Z3Prover/z3)
- Tested on Apple clang version 14.0.0 and GNU 9.3.0

Code for the plan recognition and planning effort in ToMCAT.

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

## Running the MCTS HTN Planner
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

# Acknowledgments

The C++ implementation of the
[PyHOP](https://bitbucket.org/dananau/pyhop/src/master/) planning algorithm
borrows from
[PCfVW/Simple-HTN-Planner](https://github.com/PCfVW/Simple-HTN-Planner).
