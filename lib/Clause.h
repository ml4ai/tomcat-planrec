#pragma once

#include <vector>

#include "Literal.h"

struct Clause {
    std::vector<Literal> literals;
};
