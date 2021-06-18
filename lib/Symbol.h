#pragma once

#include <string>
#include <iostream>

struct Symbol {
    std::string name;
    std::string str() const { return this->name; }

    // Support for printing symbols
    friend std::ostream& operator<<(std::ostream& out, const Symbol& symbol) {
        out << symbol.str();
        return out;
    };
};
