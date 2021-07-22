#pragma once

#include "Symbol.h"
#include <boost/exception/all.hpp>

namespace fol {
    struct Variable : Symbol {
        friend bool operator==(const Variable& lhs, const Variable& rhs) {
            return (lhs.name == rhs.name);
        };

        friend std::ostream& operator<<(std::ostream& out,
                                        const Variable& var) {
            out << "Variable(" << var.name << ")";
            return out;
        };
    };
} // namespace fol
