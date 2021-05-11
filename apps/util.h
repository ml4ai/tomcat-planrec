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
using bTasks = std::pair<bool, Tasks>;
using Plans = std::vector<bTasks>;

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
