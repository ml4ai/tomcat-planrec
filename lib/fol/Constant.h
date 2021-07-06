#pragma once

#include "Symbol.h"

namespace fol {
    struct Constant : Symbol {
        friend bool operator==(const Constant &lhs, const Constant &rhs) {
                bool eq=false;
                if (lhs.name == rhs.name) {
                    eq=true; // any variable means they aren't unified
                }
                return eq; // add condition where each element are equal
            }
    };
} // namespace fol
