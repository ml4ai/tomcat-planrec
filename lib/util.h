#pragma once

#include <iostream>
#include <iterator>
#include <random>
#include <string>
#include <variant>
#include <vector>

// Utility method to see if an element is in an associative container
template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

// Utility method to see if an element is in a vector
template <class Element> bool in(Element element, std::vector<Element> v) {
    return std::count(v.begin(), v.end(), element);
}

// select_randomly taken from
// https://stackoverflow.com/questions/6942273/how-to-get-a-random-element-from-a-c-container
template <typename Iter, typename RandomGenerator>
Iter select_randomly(Iter start, Iter end, RandomGenerator& g) {
    std::uniform_int_distribution<> dis(0, std::distance(start, end) - 1);
    std::advance(start, dis(g));
    return start;
}

template <typename Iter> Iter select_randomly(Iter start, Iter end, int seed) {
    static std::mt19937 gen(seed);
    return select_randomly(start, end, gen);
}

template <typename Iter> Iter select_randomly(Iter start, Iter end) {
    static std::random_device rd;
    static std::mt19937 gen(rd());
    return select_randomly(start, end, gen);
}

int sample_method(std::vector<int> mds, std::vector<double> wts, int seed) {
    std::mt19937 gen(seed);
    std::discrete_distribution<int> dist(wts.begin(), wts.end());
    int s = dist(gen);
    return mds[s];
}

int sample_method(std::vector<int> mds, std::vector<double> wts) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::discrete_distribution<int> dist(wts.begin(), wts.end());
    int s = dist(gen);
    return mds[s];
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
    os << "(";
    for (int i = 0; i < v.size(); i++) {
        os << v.at(i);
        if (i < v.size() - 1) {
            os << " ";
        }
    }
    os << ')';
    return os;
}

template <typename T> constexpr auto type_name() noexcept {
    std::string_view name = "Error: unsupported compiler", prefix, suffix;
#ifdef __clang__
    name = __PRETTY_FUNCTION__;
    prefix = "auto type_name() [T = ";
    suffix = "]";
#elif defined(__GNUC__)
    name = __PRETTY_FUNCTION__;
    prefix = "constexpr auto type_name() [with T = ";
    suffix = "]";
#elif defined(_MSC_VER)
    name = __FUNCSIG__;
    prefix = "auto __cdecl type_name<";
    suffix = ">(void) noexcept";
#endif
    name.remove_prefix(prefix.size());
    name.remove_suffix(suffix.size());
    return name;
}
