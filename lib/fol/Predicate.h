#pragma once

#include "Symbol.h"

namespace fol {
    // For now, we will use Predicate as a typedef for std::string, since there
    // is not the need (yet) to distinguish between predicates and regular
    // strings. In other words, we are not placing any restrictions on the
    // string, so it's simpler to use a typedef rather than a struct with a
    // name attribute.
    using Predicate = std::string;
} // namespace fol
