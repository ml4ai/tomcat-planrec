cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)

find_package(Boost COMPONENTS program_options json REQUIRED)
find_path(HIREDIS_HEADER hiredis)
find_library(HIREDIS_LIB hiredis)
find_path(REDIS_PLUS_PLUS_HEADER sw)
find_library(REDIS_PLUS_PLUS_LIB redis++)



add_executable(parse_map_info parse_map_info.cpp)
target_include_directories(parse_map_info PRIVATE ${Boost_INCLUDE_DIR} ../../lib) 
target_link_libraries(parse_map_info PRIVATE ${Boost_LIBRARIES})

add_executable(redis_to_json redis_to_json.cpp)
target_include_directories(redis_to_json PRIVATE ${Boost_INCLUDE_DIR} ${HIREDIS_HEADER} ${REDIS_PLUS_PLUS_HEADER} ../../lib)
target_link_libraries(redis_to_json PRIVATE ${Boost_LIBRARIES} ${HIREDIS_LIB} ${REDIS_PLUS_PLUS_LIB})
