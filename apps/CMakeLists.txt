set(CMAKE_CXX_STANDARD 20)

find_package(Boost COMPONENTS graph REQUIRED)
add_executable(simple_travel_planner simple_travel_planner.cpp)
add_executable(simple_sar_planner simple_sar_planner.cpp)
add_executable(simple_sar_MCTS_planner simple_sar_MCTS_planner.cpp)

target_include_directories(simple_travel_planner PRIVATE ${Boost_INCLUDE_DIR})
target_include_directories(simple_sar_planner PRIVATE ${Boost_INCLUDE_DIR})
target_include_directories(simple_sar_MCTS_planner PRIVATE ${Boost_INCLUDE_DIR})
