cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)

find_package(nlohmann_json REQUIRED)

add_executable(action_parser action_parser.cpp)
target_link_libraries(action_parser PRIVATE nlohmann_json::nlohmann_json)
