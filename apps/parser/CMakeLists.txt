set(CMAKE_CXX_STANDARD 20)

find_package(Boost REQUIRED)
add_executable(parser parser.cpp domain.cpp)
target_include_directories(parser PRIVATE ${Boost_INCLUDE_DIR})

# KB testing
add_executable(kb kb.cpp)
target_include_directories(kb PRIVATE ${Boost_INCLUDE_DIR})
