cmake_minimum_required(VERSION 3.16)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/../cmake")

list(APPEND CMAKE_PREFIX_PATH "/Users/lorenchamplin/libtorch")

find_package(Torch REQUIRED)

add_executable(regression regression.cpp)
target_link_libraries(regression "${TORCH_LIBRARIES}")
