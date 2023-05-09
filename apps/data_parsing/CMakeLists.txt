cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)

find_package(Boost COMPONENTS program_options json REQUIRED)

add_executable(parse_map_info parse_map_info.cpp)
target_include_directories(parse_map_info PRIVATE ${Boost_INCLUDE_DIR} ../../lib) 
target_link_libraries(parse_map_info PRIVATE ${Boost_LIBRARIES})
