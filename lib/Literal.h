#pragma once

#include <string>
#include "fol/Function.h"

struct Literal {
    std::string predicate;
    std::vector<ast::Term> args = {};
    bool is_negated = false;
};
