#pragma once

#include <string>
#include <iostream>

struct Symbol {
    const std::string name;
    std::string str() const { return this->name; }

    // Equality operator
    bool operator==(Symbol const& rhs) const { return this->name == rhs.name; }

    // Support for printing symbols
    friend std::ostream& operator<<(std::ostream& out, const Symbol& symbol) {
        out << symbol.str();
        return out;
    };
};
