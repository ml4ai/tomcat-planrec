#pragma once

#include "Symbol.h"

namespace fol {
    struct Variable : Symbol {
        friend bool operator==(const Variable &lhs, const Variable &rhs) {
            return (lhs.name == rhs.name);
    };
    };
}
