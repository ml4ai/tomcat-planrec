set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED)
add_executable(parser parser.cpp)
target_include_directories(parser PRIVATE ${Boost_INCLUDE_DIR})
