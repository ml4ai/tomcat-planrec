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
include test/CMakeFiles/test_unification.dir/depend.make

# Include the progress variables for this target.
include test/CMakeFiles/test_unification.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/test_unification.dir/flags.make

test/CMakeFiles/test_unification.dir/test_unification.cpp.o: test/CMakeFiles/test_unification.dir/flags.make
test/CMakeFiles/test_unification.dir/test_unification.cpp.o: ../test/test_unification.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object test/CMakeFiles/test_unification.dir/test_unification.cpp.o"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && /Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/test_unification.dir/test_unification.cpp.o -c /Users/liangzhang/CLionProjects/tomcat-planrec/test/test_unification.cpp

test/CMakeFiles/test_unification.dir/test_unification.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/test_unification.dir/test_unification.cpp.i"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && /Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/liangzhang/CLionProjects/tomcat-planrec/test/test_unification.cpp > CMakeFiles/test_unification.dir/test_unification.cpp.i

test/CMakeFiles/test_unification.dir/test_unification.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/test_unification.dir/test_unification.cpp.s"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && /Library/Developer/CommandLineTools/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/liangzhang/CLionProjects/tomcat-planrec/test/test_unification.cpp -o CMakeFiles/test_unification.dir/test_unification.cpp.s

# Object files for target test_unification
test_unification_OBJECTS = \
"CMakeFiles/test_unification.dir/test_unification.cpp.o"

# External object files for target test_unification
test_unification_EXTERNAL_OBJECTS =

test/test_unification: test/CMakeFiles/test_unification.dir/test_unification.cpp.o
test/test_unification: test/CMakeFiles/test_unification.dir/build.make
test/test_unification: test/CMakeFiles/test_unification.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable test_unification"
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_unification.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
test/CMakeFiles/test_unification.dir/build: test/test_unification

.PHONY : test/CMakeFiles/test_unification.dir/build

test/CMakeFiles/test_unification.dir/clean:
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test && $(CMAKE_COMMAND) -P CMakeFiles/test_unification.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/test_unification.dir/clean

test/CMakeFiles/test_unification.dir/depend:
	cd /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /Users/liangzhang/CLionProjects/tomcat-planrec /Users/liangzhang/CLionProjects/tomcat-planrec/test /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test /Users/liangzhang/CLionProjects/tomcat-planrec/cmake-build-debug/test/CMakeFiles/test_unification.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : test/CMakeFiles/test_unification.dir/depend

