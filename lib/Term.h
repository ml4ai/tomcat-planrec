#pragma once

#include <variant>
#include "Constant.h"
#include "Variable.h"

// Forward declare Function
struct Function;

using Term = std::variant<Constant, Variable, Function>;
