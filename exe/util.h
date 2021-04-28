#pragma once
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

using Args = std::unordered_map<std::string, std::string>;
using Task = std::pair<std::string, Args>;
using Tasks = std::vector<Task>;
using bTasks = std::pair<bool, Tasks>;
using Plans = std::vector<bTasks>;
