# Planner and Plan Recognizer Status
## Planner
- Runs hddl domain and problem defintions.
- Currently treats tasks as being total ordered regardless of ordering
  constraints given. 
- Ordering constraints will be featured in the next iteration. 
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
- Does not currently support ordering constraints for subtasks, they are
  assumed to be totally ordered in the order that they are listed in the method
  definition from top to bottom. 
- Ordering constraints for subtasks will be featured in the next iteration of the loader. 

## Problem Definition Loader
- Completed.
- See tomcat/test/test\_loader.cpp for examples of usage.


