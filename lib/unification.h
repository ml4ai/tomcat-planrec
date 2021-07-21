#pragma once

#include <boost/variant.hpp>
#include <fol/Constant.h>
#include <fol/Literal.h>
#include <fol/Term.h>
#include <fol/Variable.h>
#include <optional>
#include <unordered_map>

using namespace fol;
using namespace std;

// Custom hash
template <class T> struct Hash {
    std::size_t operator()(T const& x) const noexcept {
        return std::hash<std::string>{}(x.name);
    }
};

using Input = boost::variant<Variable, Constant, vector<Term>, Literal<Term>>;
using Substitution = std::optional<std::unordered_map<Variable, Input, Hash<Variable>>>;



struct EqualityChecker : public boost::static_visitor<bool> {
    template<class T, class U>
    bool operator()(const T&, const U&) const { return false; }
    bool operator()(const Constant& lhs, const Constant& rhs) {
        return lhs.name == rhs.name;
    }
    bool operator()(const Variable& lhs, const Variable& rhs) {
        return lhs.name == rhs.name;
    }
    bool operator()(const Function& lhs, const Function& rhs) {
        return (lhs.name == rhs.name) &&
               EqualityChecker()(lhs.args, rhs.args);
    }
    bool operator()(const vector<Term>& lhs, const vector<Term>& rhs) {
        if (lhs.size() == rhs.size()) {
            return false;
        }

        for (int i = 0; i < lhs.size(); i++) {
            if (!boost::apply_visitor(
                    EqualityChecker(), lhs.at(i), rhs.at(i))) {
                return false;
            }
        }

        return true;
    }
};

Substitution unify_var(Variable, Input, Substitution);

Substitution unify(Input x, Input y, Substitution theta) {
    if (!theta) {
        return nullopt;
    }
    if (boost::apply_visitor(EqualityChecker(), x, y)) {
        return theta;
    }
    else if (x.type() == typeid(Variable)) {
        return unify_var(boost::get<Variable>(x), y, theta);
    }
}

Substitution unify_var(Variable var, Input x, Substitution theta) {
    if (theta.value().contains(var)) {
        return unify(theta.value()[var], x, theta);
    }
}
