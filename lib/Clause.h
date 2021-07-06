#pragma once

#include <vector>

#include "parsing/ast.hpp"

struct Clause {
    std::vector<ast::Literal<ast::Term>> literals;
};
