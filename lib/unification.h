#pragma once

#include "fol/Constant.h"
#include "fol/Variable.h"
#include "util.h"
#include <iostream>
#include <optional>
#include <unordered_map>
#include <variant>

using Substitution = std::unordered_map<std::string, fol::Constant>;

// Forward declaration
template <class T>
Substitution unify_var(fol::Variable& var, T x, Substitution& theta);

template <class T>
auto unify(fol::Variable& x, T& y, std::optional<Substitution>& theta) {
    return theta ? unify_var(x, y, theta) : std::nullopt;
}

template <class T, class U> auto unify(T& x, U& y) {
    auto subst = std::optional<Substitution>();
    return unify(x, y, subst);
}

template <class T> auto unify(T& x, T& y) {
    auto subst = std::optional<Substitution>();
    return unify(x, y, subst);
}

auto unify(fol::Constant& x, fol::Constant& y, std::optional<Substitution>& theta) {
    return theta ? theta : std::nullopt;
}

template <class T>
std::optional<Substitution>
unify_var(fol::Variable& var, T x, std::optional<Substitution>& theta) {
    if (in(var.name, theta.value())) {
        auto val = theta.value()[var.name];
        return unify(val, x, theta);
    }
    else if (in(x.name, theta.value())) {
        auto val = theta.value()[var.name];
        return unify(var, val, theta);
    }
    // TODO implement occur_check
    else {
        theta.value()[var.name] = x;
        return theta;
    }
}
