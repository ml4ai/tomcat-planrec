#pragma once

#include <variant>
#include "boost/variant.hpp"
#include "Constant.h"
#include "Variable.h"

// Forward declare Function
struct Function;

using Term = boost::variant<Constant, Variable, Function>;
