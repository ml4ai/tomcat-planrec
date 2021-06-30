#pragma once

#include "Predicate.h"
#include <vector>

namespace fol {
    template <class T>
    struct Literal {
        Predicate predicate;
        std::vector<T> args;
        bool is_negative=false;
    };
}
