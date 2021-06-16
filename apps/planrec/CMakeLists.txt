cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

find_package(Boost COMPONENTS graph REQUIRED)
find_package(nlohmann_json 3.9.1 REQUIRED)
find_package(Graphviz)


# Simple SAR domain using Monte Carlo Tree Search
add_executable(simple_sar_MCTS_planrec simple_sar_MCTS_planrec.cpp)
target_include_directories(simple_sar_MCTS_planrec PRIVATE ${Boost_INCLUDE_DIR}
    ../../lib/cpphop)
target_include_directories(simple_sar_MCTS_planrec PRIVATE ${GRAPHVIZ_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(simple_sar_MCTS_planrec PRIVATE ${GRAPHVIZ_LIBS})
