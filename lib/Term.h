#pragma once

#include "Constant.h"
#include "Variable.h"
#include <boost/variant/recursive_wrapper.hpp>

struct Function;

using Term =
    boost::variant<Constant, Variable, boost::recursive_wrapper<Function>>;
