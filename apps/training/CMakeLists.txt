cmake_minimum_required(VERSION 3.19)

set(CMAKE_CXX_STANDARD 20)

#This adds debugger symbols for lldb during compilation when uncommented.
#set(CMAKE_CXX_FLAGS "-glldb")

find_package(Boost REQUIRED program_options)
find_package(nlohmann_json REQUIRED)

# Training CFM from data for team comp sar domain
add_executable(team_comp_cfm_training team_comp_cfm_training.cpp)
target_include_directories(team_comp_cfm_training PRIVATE ${Boost_INCLUDE_DIR}
    ../../lib/cpphop)
target_link_libraries(team_comp_cfm_training PRIVATE Boost::program_options nlohmann_json::nlohmann_json)
