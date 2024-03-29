cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../cmake")

#This adds debugger symbols for lldb during compilation when uncommented. 
#set(CMAKE_CXX_FLAGS "-glldb")

find_package(Boost COMPONENTS program_options json REQUIRED)
find_package(Graphviz REQUIRED)
find_package(Z3 REQUIRED)
find_path(HIREDIS_HEADER hiredis)
find_library(HIREDIS_LIB hiredis)
find_path(REDIS_PLUS_PLUS_HEADER sw)
find_library(REDIS_PLUS_PLUS_LIB redis++)

add_executable(MCTS_planrec MCTS_planrec.cpp)
target_include_directories(MCTS_planrec PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIRS} ${Z3_CXX_INCLUDE_DIRS}
    ${HIREDIS_HEADER} ${REDIS_PLUS_PLUS_HEADER} ../../lib/)
target_link_libraries(MCTS_planrec PRIVATE tomcat ${GRAPHVIZ_LIBS} ${Boost_LIBRARIES} ${Z3_LIBRARIES} ${HIREDIS_LIB} ${REDIS_PLUS_PLUS_LIB})

add_executable(planlib_planrec planlib_planrec.cpp)
target_include_directories(planlib_planrec PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIRS} ${Z3_CXX_INCLUDE_DIRS}
    ../../lib/)
target_link_libraries(planlib_planrec PRIVATE tomcat ${GRAPHVIZ_LIBS} ${Boost_LIBRARIES} ${Z3_LIBRARIES})

add_executable(planlib_prEval planlib_prEval.cpp)
target_include_directories(planlib_prEval PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIRS} ${Z3_CXX_INCLUDE_DIRS}
    ../../lib/)
target_link_libraries(planlib_prEval PRIVATE tomcat ${GRAPHVIZ_LIBS} ${Boost_LIBRARIES} ${Z3_LIBRARIES})
