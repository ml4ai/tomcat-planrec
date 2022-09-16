# Planner and Plan Recognizer Status
## Planner
- Runs hddl domain and problem defintions.
- Can now handle ordering constraints on tasks, unconstrained tasks, and task
  interleaving. 
- Has diffculties with shallow deadend and potientially infinite
  recursive/looping tasks. 
- see README in root directory (tomcat-planrec) for instructions on how to run
  the planner. 

## Plan Recognizer
- Not usable.

## Domain Definition Loader
- First iteration of the HDDL Domain Definition Loader is complete. 
- See tomcat/test/test\_loader.cpp for examples of usage.
- Does not currently support the "either" keyword.
- Correctly parses HDDL ordering constraints.

## Problem Definition Loader
- Completed.
- See tomcat/test/test\_loader.cpp for examples of usage.


