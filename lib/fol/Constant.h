#pragma once

#include "Symbol.h"

namespace fol {
    struct Constant : Symbol {
        friend bool operator==(const Constant& lhs, const Constant& rhs) {
            return (lhs.name == rhs.name);
        };
        friend std::ostream& operator<<(std::ostream& out, const Constant& c) {
            out << "Constant(" << c.name << ")";
            return out;
        };
    };
} // namespace fol
