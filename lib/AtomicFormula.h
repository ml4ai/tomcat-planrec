#pragma once

#include <vector>
#include "Predicate.h"
#include "Term.h"

struct AtomicFormula {
    Predicate predicate;
    std::vector<Term> args;
};
