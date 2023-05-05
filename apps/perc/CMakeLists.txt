project(ProjectName)
find_package(PahoMqttCpp REQUIRED)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_definitions(-DBOOST_LOG_DYN_LINK)
find_package(Z3 REQUIRED)
find_package(
    Boost 
    COMPONENTS 
    filesystem
    date_time
    chrono
    program_options
    coroutine
    json
    log
    REQUIRED
)
find_path(HIREDIS_HEADER hiredis)
find_library(HIREDIS_LIB hiredis)
find_path(REDIS_PLUS_PLUS_HEADER sw)
find_library(REDIS_PLUS_PLUS_LIB redis++)
add_executable(main main.cpp)
target_link_libraries(main PahoMqttCpp::paho-mqttpp3 ${Boost_LIBRARIES}
  ${Z3_LIBRARIES} ${HIREDIS_LIB} ${REDIS_PLUS_PLUS_LIB})
target_include_directories(main PRIVATE ${Boost_INCLUDE_DIR} ${HIREDIS_HEADER}
  ${REDIS_PLUS_PLUS_HEADER} ../../lib)

add_executable(redis_test redis_test.cpp)
target_link_libraries(redis_test ${HIREDIS_LIB} ${REDIS_PLUS_PLUS_LIB})
target_include_directories(redis_test PRIVATE ${HIREDIS_HEADER} ${REDIS_PLUS_PLUS_HEADER})
