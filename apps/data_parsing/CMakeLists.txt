cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)

find_package(nlohmann_json REQUIRED)

add_executable(team_sar_action_parsing team_sar_action_parsing.cpp)
target_link_libraries(team_sar_action_parsing PRIVATE nlohmann_json::nlohmann_json)
