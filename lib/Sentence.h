#pragma once

#include <vector>
#include <variant>
#include "Literal.h"
#include "Clause.h"

using Sentence = std::variant<Literal, Clause>;
