# HTN Planner
This code executes an HTN planner based off of SHOP and PYHOP. It is written in
C++

# Requirements
- C++20
- Boost (Tested on version 1.71.0)
- cmake (Tested on version 3.19.5)
- Tested with gcc compiler (version 9.3.0), but could possibly work with clang. 

# Building planner
To build:

    mkdir build
    cd build
    cmake ..
    make -j

# Generate plans for Simple Travel Domain
To run:

    ./simple_travel_planner
