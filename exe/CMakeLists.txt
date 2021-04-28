set(CMAKE_CXX_STANDARD 20)
set(Boost_NO_BOOST_CMAKE ON)
find_package(Boost COMPONENTS graph REQUIRED)

include_directories(${Boost_INCLUDE_DIR})

add_executable(planner planner.cpp)
