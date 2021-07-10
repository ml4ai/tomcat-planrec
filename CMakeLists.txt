project(tomcat-planrec)
cmake_minimum_required(VERSION 3.17)

set(CMAKE_CXX_STANDARD 20)

add_subdirectory(apps)
add_subdirectory(lib)

enable_testing()
add_subdirectory(test)
