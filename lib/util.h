#pragma once

#include <string>
#include <vector>
#include <random>
#include <iterator>
#include <variant>
#include <iostream>


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

// Helpers for std::visit
template <class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


// Support for printing variants
template <typename T, typename... Ts>
std::ostream& operator<<(std::ostream& os, const std::variant<T, Ts...>& v) {
    std::visit([&os](auto&& arg) { os << arg; }, v);
    return os;
}

// Define support for printing vectors
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
    os << "( ";
    for (auto x : v) {
        os << x << ' ';
    }
    os << ')';
    return os;
}

