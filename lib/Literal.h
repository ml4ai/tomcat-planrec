#pragma once

#include <string>
#include "Function.h"

struct Literal {
    std::string predicate;
    std::vector<Term> args = {};
    bool is_negated = false;
};
