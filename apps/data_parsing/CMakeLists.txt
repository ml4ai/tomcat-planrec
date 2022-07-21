cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED program_options)
find_package(nlohmann_json REQUIRED)

add_executable(parse_map_info parse_map_info.cpp)
target_include_directories(parse_map_info PRIVATE ${Boost_INCLUDE_DIR} ../../lib) 
target_link_libraries(parse_map_info PRIVATE ${Boost_LIBRARIES} Boost::program_options nlohmann_json::nlohmann_json)

add_executable(team_comp_sar_action_parsing team_comp_sar_action_parsing.cpp)
target_include_directories(team_comp_sar_action_parsing PRIVATE ${Boost_INCLUDE_DIR} ../../lib/cpphop) 
target_link_libraries(team_comp_sar_action_parsing PRIVATE ${Boost_LIBRARIES} Boost::program_options nlohmann_json::nlohmann_json)

add_executable(team_fov_parsing team_fov_parsing.cpp)
target_link_libraries(team_fov_parsing PRIVATE nlohmann_json::nlohmann_json)
