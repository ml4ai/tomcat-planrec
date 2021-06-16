#cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED)

add_executable(test_parser test_parser.cpp)
target_link_libraries(test_parser tomcat)
target_include_directories(test_parser PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# KB testing
add_executable(test_kb test_kb.cpp)
target_include_directories(test_kb PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# Test unification
add_executable(test_unification test_unification.cpp)
target_include_directories(test_unification PRIVATE ${Boost_INCLUDE_DIR} ../lib)

#add_test(NAME test_parser COMMAND test_parser -- ../../test/test.pddl)
add_test(NAME test_parser COMMAND test_parser -- ../../test/test_problem.pddl)
add_test(NAME test_kb COMMAND test_kb)
add_test(NAME test_unification COMMAND test_unification)
