# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.19

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Disable VCS-based implicit rules.
% : %,v


# Disable VCS-based implicit rules.
% : RCS/%


# Disable VCS-based implicit rules.
% : RCS/%,v


# Disable VCS-based implicit rules.
% : SCCS/s.%


# Disable VCS-based implicit rules.
% : s.%


.SUFFIXES: .hpux_make_needs_suffix_list


# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /Applications/CLion.app/Contents/bin/cmake/mac/bin/cmake

# The command to remove a file.
RM = /Applications/CLion.app/Contents/bin/cmake/mac/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /Users/liangzhang/CLionProjects/tomcat-planrec

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug

# Include any dependencies generated for this target.
include test/CMakeFiles/test_kb.dir/depend.make

# Include the progress variables for this target.
include test/CMakeFiles/test_kb.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/test_kb.dir/flags.make

test/CMakeFiles/test_kb.dir/test_kb.cpp.o: test/CMakeFiles/test_kb.dir/flags.make
test/CMakeFiles/test_kb.dir/test_kb.cpp.o: ../test/test_kb.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object test/CMakeFiles/test_kb.dir/test_kb.cpp.o"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && /Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/test_kb.dir/test_kb.cpp.o -c /Users/liangzhang/CLionProjects/tomcat-planrec/test/test_kb.cpp

test/CMakeFiles/test_kb.dir/test_kb.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_kb.dir/test_kb.cpp.i"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && /Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/liangzhang/CLionProjects/tomcat-planrec/test/test_kb.cpp > CMakeFiles/test_kb.dir/test_kb.cpp.i

test/CMakeFiles/test_kb.dir/test_kb.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_kb.dir/test_kb.cpp.s"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && /Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/liangzhang/CLionProjects/tomcat-planrec/test/test_kb.cpp -o CMakeFiles/test_kb.dir/test_kb.cpp.s

# Object files for target test_kb
test_kb_OBJECTS = \
"CMakeFiles/test_kb.dir/test_kb.cpp.o"

# External object files for target test_kb
test_kb_EXTERNAL_OBJECTS =

test/test_kb: test/CMakeFiles/test_kb.dir/test_kb.cpp.o
test/test_kb: test/CMakeFiles/test_kb.dir/build.make
test/test_kb: test/CMakeFiles/test_kb.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable test_kb"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_kb.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/CMakeFiles/test_kb.dir/build: test/test_kb

.PHONY : test/CMakeFiles/test_kb.dir/build

test/CMakeFiles/test_kb.dir/clean:
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && $(CMAKE_COMMAND) -P CMakeFiles/test_kb.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/test_kb.dir/clean

test/CMakeFiles/test_kb.dir/depend:
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /Users/liangzhang/CLionProjects/tomcat-planrec /Users/liangzhang/CLionProjects/tomcat-planrec/test /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test/CMakeFiles/test_kb.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : test/CMakeFiles/test_kb.dir/depend
