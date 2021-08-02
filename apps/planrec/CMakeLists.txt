cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../cmake")

#This adds debugger symbols for lldb during compilation when uncommented.
set(CMAKE_CXX_FLAGS "-glldb")

find_package(Boost REQUIRED)
find_package(nlohmann_json REQUIRED)
find_package(Graphviz)


# Simple SAR domain using Monte Carlo Tree Search
add_executable(simple_sar_MCTS_planrec simple_sar_MCTS_planrec.cpp)
target_include_directories(simple_sar_MCTS_planrec PRIVATE ${Boost_INCLUDE_DIR}
    ../../lib/cpphop)
target_include_directories(simple_sar_MCTS_planrec PRIVATE ${GRAPHVIZ_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(simple_sar_MCTS_planrec PRIVATE ${GRAPHVIZ_LIBS})

# Team SAR domain, using MCTS plan rec from data
add_executable(team_sar_planrec_from_data team_sar_planrec_from_data.cpp)
target_include_directories(team_sar_planrec_from_data PRIVATE ${Boost_INCLUDE_DIR}
    ../../lib/cpphop)
target_include_directories(team_sar_planrec_from_data PRIVATE ${GRAPHVIZ_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(team_sar_planrec_from_data PRIVATE ${GRAPHVIZ_LIBS})
