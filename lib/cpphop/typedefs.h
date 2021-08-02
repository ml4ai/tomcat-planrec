#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

using Args = std::unordered_map<std::string, std::string>;
using Tasks = std::vector<Task>;
using pTasks = std::pair<double, Tasks>;
using Plans = std::vector<pTasks>;

struct Task {
  std::string name;
  Args args;
  std::vector<std::string> args_order;
  Task(std::string n, Args a, std::vector<Std::string> a_o) {
    name = n;
    args = a;
    args_order = a_o;
  }
};

template <class State> using Operator = std::optional<State> (*)(State, Args);

template <class State> using pOperator = double (*)(State,State,Args);

template <class State>
using Operators = std::unordered_map<std::string, Operator<State>>;

template <class State>
using pOperators = std::unordered_map<std::string, pOperator<State>>;

template <class State> using Method = pTasks (*)(State, Args);

template <class State>
using Methods = std::unordered_map<std::string, std::vector<Method<State>>>;
