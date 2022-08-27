# Planner and Plan Recognizer Status
## Planner
-Currently runs only cpp domain defintions

## Plan Recognizer
-Currently runs only cpp domain defintions

## Domain Definition Loader
- First iteration of the HDDL Domain Definition Loader is complete. 
- See tomcat/test/test\_loader.cpp for examples of usage.
- Does not currently support the "either" keyword.
- Does not currently support ordering constraints for subtasks, they are
  assumed to be totally ordered in the order that they are listed in the method
  definition from top to bottom. 
- Ordering constraints for subtasks will be featured in the next iteration of the loader. 

## Problem Definition Loader
- Not yet completed.


