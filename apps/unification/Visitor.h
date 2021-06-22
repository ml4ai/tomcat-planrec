#pragma once

#include <string>
#include <vector>
#include "Function.h"
#include "Constant.h"
#include "Variable.h"
#include "boost/variant.hpp"


class type_visitor : public boost::static_visitor<std::string>
    {
    public:
        std::string operator()(Constant x) const {
            return "Constant";
        }
        std::string operator()(Variable x) const {
            return "Variable";
        }
        std::string operator()(Function x) const { //trouble getting this to compile
            return "Predicate";
        }
    };

