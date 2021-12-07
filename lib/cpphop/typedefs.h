#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

using Args = std::unordered_map<std::string, std::string>;

struct Task {
  std::string task_id;
  Args args;
  std::vector<std::string> args_order;
  std::vector<std::string> agents;
  Task(std::string t_id, Args a, std::vector<std::string> a_o, std::vector<std::string> as) {
    task_id = t_id;
    args = a;
    args_order = a_o;
    agents = as; 
  }
};

using Tasks = std::vector<Task>;
using pTasks = std::pair<double, Tasks>;
using cTasks = std::pair<std::string, Tasks>;
using Plans = std::vector<pTasks>;
using cPlans = std::vector<cTasks>;

using CFM = std::unordered_map<std::string, std::unordered_map<std::string, std::unordered_map<std::string,int>>>;
using CPM = std::unordered_map<std::string, std::unordered_map<std::string, std::unordered_map<std::string,double>>>;


template <class State> using Operator = std::optional<State> (*)(State, Args);

template <class State> using pOperator = double (*)(State,State,Args);

template <class State>
using Operators = std::unordered_map<std::string, Operator<State>>;

template <class State>
using pOperators = std::unordered_map<std::string, pOperator<State>>;

template <class State> using Method = pTasks (*)(State, Args);

template <class State> using cMethod = cTasks (*)(State, Args);

template <class State>
using Methods = std::unordered_map<std::string, std::vector<Method<State>>>;

template <class State>
using cMethods = std::unordered_map<std::string, std::vector<cMethod<State>>>;
