cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../cmake")

#This adds debugger symbols for lldb during compilation when uncommented. 
#set(CMAKE_CXX_FLAGS "-glldb")

find_package(Boost REQUIRED program_options)
find_package(Graphviz)
find_package(Z3 REQUIRED)

# Comp Team SAR domain using Monte Carlo Tree Search
add_executable(MCTS_planrec MCTS_planrec.cpp)
target_include_directories(MCTS_planrec PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIR} ${Z3_CXX_INCLUDE_DIRS}
    ../../lib/)
target_link_libraries(MCTS_planrec PRIVATE tomcat ${GRAPHVIZ_LIBS} Boost::program_options ${Z3_LIBRARIES})
