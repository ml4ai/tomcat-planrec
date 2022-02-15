set(CMAKE_CXX_STANDARD 20)

# We require a minimum of Boost 1.76, since we need this bugfix: https://github.com/boostorg/spirit/commit/bcf19220896a73523f20fdc4a56ad553a21c5292
find_package(Boost 1.76 REQUIRED)
add_library(tomcat parsing/parser_instantiation.cpp parsing/ast.cpp fol/FOLDomain.h)
target_include_directories(tomcat PRIVATE ${Boost_INCLUDE_DIR})
