#include <iostream>
#include "typedefs.h"

void print(Tasks tasks) {
    std::cout << "[";
    for (auto task : tasks) {
        std::cout << "(";
        std::cout << task.first << ",";
        for (auto [k, v] : task.second) {
            std::cout << v << ",";
        }
        std::cout << ")";
    }
    std::cout << "]";
    std::cout << std::endl;
}

std::string task2string(Task task) {
  std::string stask = "(" + task.first + ",";
  for (auto [k, v] : task.second) {
    stask += v + ",";
  }
  stask += ")";

  return stask;
}

void print(bTasks btasks) { print(btasks.second); }

void print(Plans plans) {
    std::cout << "Plans Found:" << std::endl;
    int i = 0;
    for (auto bt : plans) {
        std::cout << "Plan " << i << ": ";
        print(bt);
        i++;
    }
}

// Utility methods for printing information to stdout.
template <class State> void print(Operators<State> operators) {
    for (auto [operator_name, operator_func] : operators) {
        std::cout << operator_name << ", ";
    }
    std::cout << std::endl;
}

template <class State> void print(Methods<State> methods) {
    for (auto [method_name, method_func] : methods) {
        std::cout << method_name << ", ";
    }
    std::cout << std::endl;
}

