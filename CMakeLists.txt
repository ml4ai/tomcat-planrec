project(tomcat-planrec)
cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/apps/cmake")
add_subdirectory(apps)
add_subdirectory(lib)

enable_testing()
add_subdirectory(test)
