#pragma once

#include<string>

// Custom hash
template <class T> struct Hash {
    std::size_t operator()(T const& x) const noexcept {
        return std::hash<std::string>{}(x.name);
    }
};

