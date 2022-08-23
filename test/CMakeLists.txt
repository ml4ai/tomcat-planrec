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


# Test unification
add_executable(test_unification test_unification.cpp)
target_link_libraries(test_unification tomcat Boost::log)
target_include_directories(test_unification PRIVATE ${Boost_INCLUDE_DIR} ../lib)

# Test cnf_conversion
# add_executable(test_cnf_conversion test_cnf_conversion.cpp ../lib/fol/FOLDomain.h)
# target_link_libraries(test_cnf_conversion tomcat)
# target_include_directories(test_cnf_conversion PRIVATE ${Boost_INCLUDE_DIR} ../lib)

add_test(NAME test_parser COMMAND test_parser)
add_test(NAME test_kb COMMAND test_kb)
add_test(NAME test_unification COMMAND test_unification)
# add_test(NAME test_cnf_conversion COMMAND test_cnf_conversion)
