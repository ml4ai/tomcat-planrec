#pragma once

#include <variant>
#include <vector>
#include "parsing/FOLNode.h"
#include "Constant.h"
#include "Variable.h"

// Forward declare Function
//struct Function;

//using Term = std::variant<Constant, Variable, Function>;
class Term: FOLNode {
	std::vector<Term> getArgs();
	Term copy();
};