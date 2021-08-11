cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED program_options)
find_package(nlohmann_json REQUIRED)

add_executable(team_sar_action_parsing team_sar_action_parsing.cpp)
target_include_directories(team_sar_action_parsing PRIVATE ${Boost_INCLUDE_DIR} ../../lib/cpphop) 
target_link_libraries(team_sar_action_parsing PRIVATE Boost::program_options nlohmann_json::nlohmann_json)
