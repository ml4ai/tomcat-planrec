#pragma once

#include "Term.h"

namespace fol {
    struct Function {
        std::string name;
        std::vector<Term> args = {};
    };
} // namespace fol
