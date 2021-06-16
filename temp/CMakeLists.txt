cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)

#No project specified. 
project(hddl_parser)

find_package(Boost COMPONENTS program_options REQUIRED)

add_executable(parser parser.cpp domain.cpp)

target_include_directories(parser PRIVATE ${Boost_INCLUDE_DIR})

target_link_libraries(parser ${Boost_LIBRARIES})
