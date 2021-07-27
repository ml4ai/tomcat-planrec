#pragma once

#include "boost/variant.hpp"
#include "fol/Constant.h"
#include "fol/Function.h"
#include "fol/Variable.h"
#include <string>
#include <vector>

class GetTermType : public boost::static_visitor<std::string> {
  public:
    std::string operator()(fol::Constant x) const { return "Constant"; }
    std::string operator()(fol::Variable x) const { return "Variable"; }
    std::string operator()(fol::Function x) const { return "Function"; }
};
