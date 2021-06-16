#pragma once

#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

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
