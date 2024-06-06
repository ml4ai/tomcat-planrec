set(CMAKE_CXX_STANDARD 20)

# We require a minimum of Boost 1.79, since we need this bugfix: https://github.com/boostorg/spirit/commit/bcf19220896a73523f20fdc4a56ad553a21c5292
# And the perceptual agent code requires json pointers only in 1.79 and above

add_compile_definitions(BOOST_NO_CXX98_FUNCTION_BASE)
find_package(Boost 1.79 COMPONENTS json REQUIRED)
find_package(Z3 REQUIRED)
find_package(Graphviz REQUIRED)
add_library(tomcat parsing/parser_instantiation.cpp parsing/ast.cpp kb.h)
target_include_directories(tomcat PRIVATE ${Boost_INCLUDE_DIR} ${Z3_CXX_INCLUDE_DIRS} ${GRAPHVIZ_INCLUDE_DIRS})
target_link_libraries(tomcat ${Boost_LIBRARIES})
