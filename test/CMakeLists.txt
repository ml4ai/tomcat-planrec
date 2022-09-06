set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../apps/cmake")

add_definitions(-DBOOST_LOG_DYN_LINK)
find_package(Boost COMPONENTS log REQUIRED)
find_package(Graphviz)
find_package(nlohmann_json REQUIRED)
find_package(Z3 REQUIRED)

# Parser testing
add_executable(test_parser test_parser.cpp)
target_link_libraries(test_parser tomcat)
target_include_directories(test_parser PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# KB testing
add_executable(test_kb test_kb.cpp)
target_link_libraries(test_kb PRIVATE tomcat)
target_link_libraries(test_kb PRIVATE ${Z3_LIBRARIES})
target_include_directories(test_kb PRIVATE ${Boost_INCLUDE_DIR} ${Z3_CXX_INCLUDE_DIRS} ../lib)

# loader testing
add_executable(test_loader test_loader.cpp)
target_link_libraries(test_loader PRIVATE tomcat)
target_link_libraries(test_loader PRIVATE ${Z3_LIBRARIES})
target_include_directories(test_loader PRIVATE ${Boost_INCLUDE_DIR} ${Z3_CXX_INCLUDE_DIRS} ../lib)

# planner testing
add_executable(test_MCTS_planner test_MCTS_planner.cpp)
target_link_libraries(test_MCTS_planner PRIVATE tomcat)
target_link_libraries(test_MCTS_planner PRIVATE ${Z3_LIBRARIES})
target_include_directories(test_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR} ${Z3_CXX_INCLUDE_DIRS} ../lib)

add_test(NAME test_parser COMMAND test_parser)
add_test(NAME test_kb COMMAND test_kb)
add_test(NAME test_loader COMMAND test_loader)
add_test(NAME test_MCTS_planner COMMAND test_MCTS_planner)
