#pragma once

#include "Symbol.h"

namespace fol {
    struct Constant : Symbol {
        friend bool operator==(const Constant &lhs, const Constant &rhs) {
            return (lhs.name == rhs.name);
    };
    };
} // namespace fol
