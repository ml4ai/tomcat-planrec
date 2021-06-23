#include "ast.hpp"

bool ast::PrimitiveType::operator==(const ast::PrimitiveType& primitive_type) const {
    return this->name == primitive_type.name;
}
