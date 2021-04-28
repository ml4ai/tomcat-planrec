set(CMAKE_CXX_STANDARD 20)
set(Boost_NO_BOOST_CMAKE ON)
find_package(Boost COMPONENTS graph REQUIRED)

include_directories(${Boost_INCLUDE_DIR})

add_executable(simple_travel_planner simple_travel_planner.cpp)
