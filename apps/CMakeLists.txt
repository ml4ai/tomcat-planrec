cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

find_package(Boost COMPONENTS graph REQUIRED)
find_package(nlohmann_json 3.9.1 REQUIRED)
find_package(Graphviz)

add_executable(simple_travel_planner simple_travel_planner.cpp)
add_executable(simple_sar_planner simple_sar_planner.cpp)
add_executable(simple_sar_MCTS_planner simple_sar_MCTS_planner.cpp)
add_executable(simple_sar_MCTS_planrec simple_sar_MCTS_planrec.cpp)

target_include_directories(simple_travel_planner PRIVATE ${Boost_INCLUDE_DIR})
target_include_directories(simple_sar_planner PRIVATE ${Boost_INCLUDE_DIR})
target_include_directories(simple_sar_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR})
target_include_directories(simple_sar_MCTS_planrec PRIVATE ${Boost_INCLUDE_DIR})
target_include_directories(simple_sar_MCTS_planrec PRIVATE ${GRAPHVIZ_INCLUDE_DIR})
target_include_directories(simple_sar_MCTS_planner PRIVATE ${GRAPHVIZ_INCLUDE_DIR})

target_link_libraries(simple_sar_MCTS_planrec PRIVATE ${GRAPHVIZ_LIBS})
target_link_libraries(simple_sar_MCTS_planner PRIVATE ${GRAPHVIZ_LIBS})
