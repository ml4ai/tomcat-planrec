set(CMAKE_CXX_STANDARD 20)
find_package(Boost REQUIRED)
add_library(tomcat parsing/parser_instantiation.cpp parsing/ast.cpp)
target_include_directories(tomcat PRIVATE ${Boost_INCLUDE_DIR})
