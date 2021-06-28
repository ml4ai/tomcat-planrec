#pragma once

#include <vector>
#include <variant>
#include "Literal.h"
#include "Clause.h"
#include "parsing/FOLNode.h"

//using Sentence = std::variant<Literal, Clause>;

class Sentence: FOLNode{
    Sentence copy();
};
