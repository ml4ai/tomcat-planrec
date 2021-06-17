set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED)
find_package(nlohmann_json REQUIRED)

# Parser testing
add_executable(test_parser test_parser.cpp)
target_link_libraries(test_parser tomcat)
target_include_directories(test_parser PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# KB testing
add_executable(test_kb test_kb.cpp)
target_include_directories(test_kb PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# Test unification
add_executable(test_unification test_unification.cpp)
target_include_directories(test_unification PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# test DFS planner 
add_executable(test_DFS_planner test_DFS_planner.cpp)
target_include_directories(test_DFS_planner PRIVATE ${Boost_INCLUDE_DIR}
  ../lib/cpphop)

# test MCTS planner 
add_executable(test_MCTS_planner test_MCTS_planner.cpp)
target_include_directories(test_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR}
  ../lib/cpphop)

add_test(NAME test_parser COMMAND test_parser -- ../../test/test_domain.pddl ../../test/test_problem.pddl)
add_test(NAME test_kb COMMAND test_kb)
add_test(NAME test_unification COMMAND test_unification)
add_test(NAME test_DFS_planner COMMAND test_DFS_planner)
add_test(NAME test_MCTS_planner COMMAND test_MCTS_planner)
