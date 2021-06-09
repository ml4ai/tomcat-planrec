#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
#include <random>
#include <iterator>

using Args = std::unordered_map<std::string, std::string>;
using Task = std::pair<std::string, Args>;
using Tasks = std::vector<Task>;
using pTasks = std::pair<double, Tasks>;
using Plans = std::vector<pTasks>;

template <class State> using Operator = std::optional<State> (*)(State, Args);

template <class State> using pOperator = double (*)(State,State,Args);

template <class State>
using Operators = std::unordered_map<std::string, Operator<State>>;

template <class State>
using pOperators = std::unordered_map<std::string, pOperator<State>>;

template <class State> using Method = pTasks (*)(State, Args);

template <class State>
using Methods = std::unordered_map<std::string, std::vector<Method<State>>>;

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

void print(pTasks ptasks) { print(ptasks.second); }

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

// Utility method to see if an element is in an associative container
template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

// Utility method to see if an element is in a vector
template <class Element>
bool in(Element element, std::vector<Element> v) {
    return std::count(v.begin(),v.end(), element);
}

//select_randomly taken from 
//https://stackoverflow.com/questions/6942273/how-to-get-a-random-element-from-a-c-container
template<typename Iter, typename RandomGenerator>
Iter select_randomly(Iter start, Iter end, RandomGenerator& g) {
    std::uniform_int_distribution<> dis(0, std::distance(start, end) - 1);
    std::advance(start, dis(g));
    return start;
}

template<typename Iter>
Iter select_randomly(Iter start, Iter end, int seed) {
    static std::mt19937 gen(seed);
    return select_randomly(start, end, gen);
}

template<typename Iter>
Iter select_randomly(Iter start, Iter end) {
    static std::random_device rd;
    static std::mt19937 gen(rd());
    return select_randomly(start, end, gen);
}

int sample_method(std::vector<int> mds, std::vector<double> wts, int seed) {
  std::mt19937 gen(seed);
  std::discrete_distribution<int> dist (wts.begin(),wts.end());
  int s = dist(gen);
  return mds[s];
}

int sample_method(std::vector<int> mds, std::vector<double> wts) {
  std::random_device rd;
  std::mt19937 gen(rd());
  std::discrete_distribution<int> dist (wts.begin(),wts.end());
  int s = dist(gen);
  return mds[s];
}
