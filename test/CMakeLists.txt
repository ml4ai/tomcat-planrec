set(CMAKE_CXX_STANDARD 20)


find_package(Boost REQUIRED)
add_executable(parser parser.cpp)
target_include_directories(parser PRIVATE ${Boost_INCLUDE_DIR} ../lib)
target_link_libraries(parser tomcat)

# KB testing
add_executable(kb kb.cpp)
target_include_directories(kb PRIVATE ${Boost_INCLUDE_DIR})
