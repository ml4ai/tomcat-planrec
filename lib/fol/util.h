#pragma once

#include "Term.h"

// Get name of term
std::string name(ast::Term term) {
    return boost::apply_visitor([](const auto& t) { return t.name; }, term);
}
