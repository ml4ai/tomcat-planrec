#pragma once

#include <string>
#include <vector>
#include "fol/Function.h"
#include "fol/Constant.h"
#include "fol/Variable.h"
#include "boost/variant.hpp"


class type_visitor : public boost::static_visitor<std::string>
    {
    public:
        std::string operator()(fol::Constant x) const {
            return "Constant";
        }
        std::string operator()(fol::Variable x) const {
            return "Variable";
        }
        std::string operator()(fol::Function x) const { 
            return "Predicate";
        }
    };

