# tomcat-planrec
Code for the plan recognition and planning effort in ToMCAT.

# Table of Contents
1. [Build Requirements](#build-requirements) 
2. [Installation](#installation) 
3. [HDDL Domain and Problem Definition
   Loaders](#hddl-domain-and-problem-definition-loaders)
4. [MCTS Hierarchical Planners](#mcts-hierarchical-planners)
    1. [MCTS HTN Planner](#mcts-htn-planner) 
    2. [MCTS Hybrid Planner](#mcts-hybrid-planner)
5. [MCTS Hierarchical Plan Recognizers](#mcts-hierarchical-plan-recognizers)
    1. [Setting Up Redis Server](#setting-up-redis-server)
    2. [Running the Plan Recognizers](#running-the-plan-recognizers)
    3. [Data Tools For Plan Recognizer Results](#data-tools-for-plan-recognizer-results)
6. [SAR Perceptual System](#sar-perceptual-system)
7. [Evaluation Procedure for MCTS HTN Plan
   Recognizer](#evaluation-procedure-for-mcts-htn-plan-recognizer)

# Build Requirements
- cmake (Minimum requirement is version 3.16, https://cmake.org/)
- Boost (Minimum requirement is version 1.79, https://www.boost.org/)
  - Specific Boost Libraries to build: filesystem, log, date\_time, chrono, program\_options, coroutine, json
- Z3 (c++ Library) (Minimum requirement is version 4.8.17, https://github.com/Z3Prover/z3)
- Graphviz (c Library) (Tested on version 8.0.5, https://graphviz.org/)
- OpenSLL (c++ Library) (Tested on version 3.1.1, https://www.openssl.org/) 
- Paho MQTT (c++ Library) (Tested on version 1.3.9)
- Hiredis (c Library) (Tested on version 0.14.1, https://redis.io/lp/hiredis/)
- Redis-Plus-Plus (c++ Library) (Tested on version 1.3.5, https://github.com/sewenew/redis-plus-plus)
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
[test\_MCTS\_planner](https://github.com/ml4ai/tomcat-planrec/blob/main/test/test_MCTS_planner.cpp) 
ran by the ctest command. 

The default domain and problem definitions are the [transport
domain](https://github.com/ml4ai/tomcat-planrec/blob/document_updating/domains/transport_domain.hddl) 
and a sample [transport problem](https://github.com/ml4ai/tomcat-planrec/blob/main/domains/transport_problem.hddl). 
The default score function is "delivery\_one" as defined in [score\_functions.h](https://github.com/ml4ai/tomcat-planrec/blob/main/domains/score_functions.h). 

Run with the help flag,

    ./apps/planners/MCTS_planner -h

To see what options are available including how to run the planner with
different domain and problem definitions and score functions. Score functions
must be predefined in a similar way to the "delivery\_one" function mentioned above. 
There are also options to run the hybrid planner (discussed below).

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
Our code-base contains two different Plan Recognition algorithms that mirror
the functionality of the two planner types detailed above. These take as input
a sequence of observed grounded actions (and other required planning elements)
and output a solution in the form of a (partial) task hierarchy that best 
estimates an explanation for the observations given a limited inference time.
Running the Plan Recognizers requires setting up a Redis server. The inputted
observations must be uploaded to this Redis server. Likewise, the outputted
solution from the Plan Recognizers are also uploaded back to this server in the
form of a json message. 

## Setting Up Redis Server
You will first need to install the Redis client and server software by
following the install instructions appriopriate for your machine (the one you
intend to host the server) found at [https://redis.io/docs/latest/get-started/](https://redis.io/docs/latest/get-started/)

Once installed, you can start the Redis server under default settings by doing,

    redis-server

in a terminal. The default port used is 6379. This can be changed using
`--port` or in a .conf file passed to the server on start-up. Use the `-h` or
go to the website to learn about other settings.

The connection to the server can be checked by running,

    redis-cli

in a seperate terminal (or machine with appriopriate hostname and port
settings). This will open up the Redis REPL to communicate directly with the
server. By default it connects to "tcp://127.0.0.1:6379", which is the local
host (i.e., same machine) through port 6379.

The server can be terminated with `control-c`. By default, it saves its database
to a file called `dump.rdb` when closed and automatically loads this file on start-up.

## Running the Plan Recognizers
To successfully run the plan recognizer, a redis server must be set-up with
observations loaded into its database under the `actions` key. This can be done
using the redis-cli REPL using the `XADD` command (see Redis documentation for
full usage) or by using our supplied
[pr\_samples\_to\_redis.cpp](https://github.com/ml4ai/tomcat-planrec/blob/main/apps/data_tools/pr_samples_to_redis.cpp) 
script.

Using the above script at this time requires you to manually hardcode a set of
observations into the
[pr_samples.h](https://github.com/ml4ai/tomcat-planrec/blob/main/domains/pr_samples.h) file.
A default set of observations are already hardcoded into this file for the
transport domain as an example. These will be loaded into the redis database by
default by running, 

    ./apps/data_tools/pr_samples_to_redis

Like other terminal command calls, use the `-h` flag to see other settings.

After having loaded observations into the redis database, you can run the
[MCTS\_planrec.cpp](https://github.com/ml4ai/tomcat-planrec/blob/main/apps/planrec/MCTS_planrec.cpp) 
script. Below is an example on how to run the default settings assuming that
server is located locally and is using port 6379. 
    
    ./apps/planrec/MCTS_planrec -a tcp://127.0.0.1:6379

The results will be automatically loaded onto the redis database on the server
with the same supplied address above under the "explanations" key. As mentioned
before, the output is a json message. It can be interacted with using the
redis-cli REPL, but we recommend using one of our supplied scripts discussed
below. Finally, the `-h` flag will reveal other plan recognition settings
including those for the hybrid planning version of the algorithm. 

## Data Tools For Plan Recognizer Results 
For convenience, we supply 3 different scripts for processing results from the
plan recognizers. 

The first is
[redis\_to\_json.cpp](https://github.com/ml4ai/tomcat-planrec/blob/main/apps/data_tools/redis_to_json.cpp) 
which by default accesses the redis database for the given redis server address
(using the `-a` flag) and looks for entries under the "explanations" key. Each
entry is converted into its own json file. The naming convention for these json
files are "explanations\_1.json", "explanations\_2.json", etc. Use the `-h` to
see other options. 

The second script is
[redis\_grapher.cpp](https://github.com/ml4ai/tomcat-planrec/blob/main/apps/data_tools/redis_grapher.cpp)
which works in a similar fashion to previously mentioned script except it
generates a visual representation (i.e., a graph) of the inferred partial task hierarchy for
each entry found under the "explanations" key. These graphs are saved as .png
files and use the same naming conventions as the first script. 

Finally,
[json\_grapher.cpp](https://github.com/ml4ai/tomcat-planrec/blob/main/apps/data_tools/json_grapher.cpp) 
does the same thing as the redis grapher, except it takes in a json file that
was outputted from the redis to json script mentioned above. 

# SAR Perceptual System
We also developed a perceptual system for the [ASIST Study 3
Testbed](https://artificialsocialintelligence.org/testbed/), 
a Minecraft Search and Rescue (SAR) mission. It uses the Paho MQTT c++ library
to subscribe to json messages from the testbed's message bus. The message bus
can be simulated by running an apprioriate Study 3 metadata file through the
[elkless-replayer](https://github.com/ml4ai/tomcat/blob/d2b4ac940b5e33a37cc503c27551e7e77cbedbce/tools/elkless_replayer#L4)
python script. 

## Actions Parsed
- (location ?agent ?current\_location ?new\_location) (An agent has moved
  locations)
- (place\_victim ?agent ?vic\_id ?location) (An agent has placed a victim at a
  location)
- (pickup\_victim ?agent ?vic\_id ?location) (An agent has picked up a victim
  at a location)
- (triage\_victim ?agent ?vic\_id ?location) (The medic has triaged a victim at
  a location)
- (rubble\_destroyed ?agent ?location) (The engineer has destroyed rubble at a
  location)
- (marker\_placed ?agent ?marker\_type ?location) (An agent has placed a marker
  at a location)
- (marker\_removed ?agent\_a ?agent\_b ?marker\_type ?location) (An agent a has
  removed agent b's marker at a location)
- (wake\_critical ?agent\_a ?agent\_b ?vic\_id ?location) (The medic and an
  assisting agent have woken a critical victim at a location)
- (victim\_evactuated ?agent ?vic\_id location) (An agent has evacuated a
  victim at a evacuation location)

## Field of View Percepts
These are percepts that are saved under the "fov" key in the redis database.
Both the planner and plan recoginizers regularly check for field of view (fov) percepts and try
to update the state according to timestamps that match their internal planning
times. 

- (fov\_victim\_regular ?agent ?vic\_id) (An agent currently sees a regular
  victim)
- (fov\_victim\_critical ?agent ?vic\_id) (An agent currently sees a critical
  victim)
- (fov\_victim\_saved ?agent ?vic\_id) (An agent currently sees a triaged
  victim)
- (fov\_gravel ?agent) (An agent currently sees gravel)
- (fov\_marker ?agent\_a ?marker\_type ?agent\_b) (An agent a currently sees a
  marker left by agent b)

## Running the Perceptual System
The perceptual system script needs to be started before the message bus (or
simulated message bus) starts publishing. Below is the default command for
doing so,

    ./apps/perc/main

By default it connects to a MQTT host locally and tries to use port 1883. 

# Evaluation Procedure for MCTS HTN Plan Recognizer
Finally, we developed a [evaluation
procedure](https://github.com/ml4ai/tomcat-planrec/blob/main/apps/eval/MCTS_planrec_eval.cpp) 
for the MCTS HTN Plan Recognizer. It does evaluation by prediction. 
Given the apprioriate redis address, it extracts the inferred task 
hierarchies (under the "explanations" key) from the database at the 
address and inputs them into our MCTS HTN Planner. It also extracts the
true grounded plan from the "actions" key. 

The planner attempts to plan from a state
initialized from the endpoint of a given task hierarchy up to some incremented
plan horizon over multiple trials. For example, if its set to do 10 trials and
the true grounded plan has a length of 5, then it will do 10 trials of planning
up to a horizon of 1, 10 trials of a planning horizon of 2, etc. up until 10
trials of a horizon of 5. In this case, the planner is ran 50 times overall.
Each trial for each horizon is matched to the corresponding subsequence within
the true grounded plan (e.g., partial plans of horizon 3 are matched to the first 3
actions in the true plan). A average accuracy over the number of trials is
computed for each planning horizon. In this way, we can see how the average
prediction accuracy decays for a given plan explanation (i.e., inferred task
hierarchy) over increasing prediction horizons. 

Running the evaluation procedure is similar to running the planning and plan
recognizer scripts. As before, there is a `-h` flag that explains the different
settings of the evaluation procedure. All results are saved to a csv file. 

