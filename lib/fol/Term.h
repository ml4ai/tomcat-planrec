#pragma once

#include "Constant.h"
#include "Variable.h"
#include <boost/variant.hpp>
#include <boost/variant/recursive_wrapper.hpp>

namespace fol {
    struct Function;

    using Term =
        boost::variant<Constant, Variable, boost::recursive_wrapper<Function>>;
} // namespace fol
