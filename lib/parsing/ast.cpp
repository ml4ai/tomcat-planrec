#include "ast.hpp"

bool ast::Nil::operator==(const ast::Nil& nil) const {
    return true;
}
