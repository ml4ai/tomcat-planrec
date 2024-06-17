cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../cmake")

add_compile_definitions(BOOST_NO_CXX98_FUNCTION_BASE)
find_package(Boost COMPONENTS program_options json REQUIRED)
find_package(Graphviz REQUIRED)
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

add_executable(json_grapher json_grapher.cpp)
target_include_directories(json_grapher PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIRS} ../../lib)
target_link_libraries(json_grapher PRIVATE ${Boost_LIBRARIES} ${GRAPHVIZ_LIBS})

add_executable(redis_grapher redis_grapher.cpp)
target_include_directories(redis_grapher PRIVATE ${Boost_INCLUDE_DIR} ${GRAPHVIZ_INCLUDE_DIRS} ${HIREDIS_HEADER} ${REDIS_PLUS_PLUS_HEADER} ../../lib)
target_link_libraries(redis_grapher PRIVATE ${Boost_LIBRARIES} ${GRAPHVIZ_LIBS} ${HIREDIS_LIB} ${REDIS_PLUS_PLUS_LIB})

add_executable(pr_samples_to_redis pr_samples_to_redis.cpp)
target_include_directories(pr_samples_to_redis PRIVATE ${Boost_INCLUDE_DIR} ${HIREDIS_HEADER} ${REDIS_PLUS_PLUS_HEADER} ../../lib)
target_link_libraries(pr_samples_to_redis PRIVATE ${Boost_LIBRARIES} ${HIREDIS_LIB} ${REDIS_PLUS_PLUS_LIB})
