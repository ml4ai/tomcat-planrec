cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../cmake")

#This adds debugger symbols for lldb during compilation when uncommented. 
#set(CMAKE_CXX_FLAGS "-glldb")

find_package(Boost REQUIRED program_options)
find_package(Graphviz)
find_package(nlohmann_json REQUIRED)

# Simple travel example, translated from PyHOP
add_executable(simple_travel_planner simple_travel_planner.cpp)
target_include_directories(simple_travel_planner PRIVATE ${Boost_INCLUDE_DIR}
    ../../lib/cpphop)

# Simple transporting example, translated from PyHOP
add_executable(simple_transporting_planner simple_transporting_planner.cpp)
target_include_directories(simple_transporting_planner PRIVATE ${Boost_INCLUDE_DIR}
        ../../lib/cpphop)

# Simple SAR domain, using PyHOP procedure (translated to C++)
add_executable(simple_sar_planner simple_sar_planner.cpp)
target_include_directories(simple_sar_planner PRIVATE ${Boost_INCLUDE_DIR}
    ../../lib/cpphop)

# Simple SAR domain using Monte Carlo Tree Search
add_executable(simple_sar_MCTS_planner simple_sar_MCTS_planner.cpp)
target_include_directories(simple_sar_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(simple_sar_MCTS_planner PRIVATE ${GRAPHVIZ_LIBS})

# Team SAR domain using Monte Carlo Tree Search
add_executable(vanilla_team_sar_MCTS_planner vanilla_team_sar_MCTS_planner.cpp)
target_include_directories(vanilla_team_sar_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(vanilla_team_sar_MCTS_planner PRIVATE ${GRAPHVIZ_LIBS})

# Comp Team SAR domain using Monte Carlo Tree Search
add_executable(team_comp_sar_MCTS_planner team_comp_sar_MCTS_planner.cpp)
target_include_directories(team_comp_sar_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(team_comp_sar_MCTS_planner PRIVATE ${GRAPHVIZ_LIBS} Boost::program_options nlohmann_json::nlohmann_json)
