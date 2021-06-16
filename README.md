# tomcat-planrec

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

# Acknowledgments

The C++ implementation of the
[PyHOP](https://bitbucket.org/dananau/pyhop/src/master/) planning algorithm
borrows from
[PCfVW/Simple-HTN-Planner](https://github.com/PCfVW/Simple-HTN-Planner).
