#pragma once

#include "Hash.h"
#include <boost/log/trivial.hpp>
#include <boost/variant.hpp>
#include <fol/Constant.h>
#include <fol/Literal.h>
#include <fol/Term.h>
#include <fol/Variable.h>
#include <optional>
#include <unordered_map>

using namespace fol;
using namespace std;

using Input = boost::variant<Term,
                             Predicate,
                             Variable,
                             Constant,
                             Function,
                             vector<Term>,
                             Literal<Term>>;

using Substitution = std::unordered_map<Variable, Input, Hash<Variable>>;

struct EqualityChecker : public boost::static_visitor<bool> {
    template <class T, class U> bool operator()(const T&, const U&) const {
        return false;
    }
    bool operator()(const Constant& lhs, const Constant& rhs) {
        return lhs.name == rhs.name;
    }
    bool operator()(const Variable& lhs, const Variable& rhs) {
        return lhs.name == rhs.name;
    }
    bool operator()(const Function& lhs, const Function& rhs) {
        return (lhs.name == rhs.name) && EqualityChecker()(lhs.args, rhs.args);
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
    bool operator()(const Predicate& lhs, const Predicate& rhs) const {
        return lhs == rhs;
    }
    bool operator()(const Term& lhs, const Term& rhs) const {
        return boost::apply_visitor(EqualityChecker(), lhs, rhs);
    }
};

std::optional<Substitution>
    unify_var(Variable, Input, std::optional<Substitution>);

std::optional<Substitution>
unify(Input x, Input y, std::optional<Substitution> theta) {
    using boost::get;
    if (theta == nullopt) {
        return nullopt;
    }
    if (boost::apply_visitor(EqualityChecker(), x, y)) {
        return theta;
    }
    else if (x.type() == typeid(Variable)) {
        return unify_var(get<Variable>(x), y, theta);
    }
    else if (y.type() == typeid(Variable)) {
        return unify_var(get<Variable>(y), x, theta);
    }
    else if (x.type() == typeid(Literal<Term>) &&
             y.type() == typeid(Literal<Term>)) {
        auto x_lit = get<Literal<Term>>(x);
        auto y_lit = get<Literal<Term>>(y);
        return unify(x_lit.args,
                     y_lit.args,
                     unify(x_lit.predicate, y_lit.predicate, theta));
    }
    else if (x.type() == typeid(Function) && y.type() == typeid(Function)) {
        auto x_func = get<Function>(x);
        auto y_func = get<Function>(y);
        return unify(
            x_func.args, y_func.args, unify(x_func.name, y_func.name, theta));
    }

    else if (x.type() == typeid(vector<Term>) &&
             y.type() == typeid(vector<Term>)) {
        auto x_vec = get<vector<Term>>(x);
        auto y_vec = get<vector<Term>>(y);
        auto x_rest = vector<Term>(x_vec.size() - 1);
        auto y_rest = vector<Term>(y_vec.size() - 1);
        for (int i = 1; i < x_vec.size(); i++) {
            x_rest.push_back(x_rest.at(i));
        }
        for (int i = 1; i < y_vec.size(); i++) {
            y_rest.push_back(y_rest.at(i));
        }

        return unify(x_rest, y_rest, unify(x_vec.at(0), y_vec.at(0), theta));
    }
    else {
        return nullopt;
    }
}

std::optional<Substitution> unify(Input x, Input y) {
    return unify(x, y, Substitution());
}

std::optional<Substitution>
unify_var(Variable var, Input x, std::optional<Substitution> theta) {
    if (theta.value().contains(var)) {
        auto val = theta.value()[var];
        return unify(val, x, theta);
    }
    else if (x.type() == typeid(Variable)) {
        auto x_var = boost::get<Variable>(x);
        if (theta.value().contains(x_var)) {
            auto val = theta.value()[x_var];
            return unify(var, val, theta);
        }
    }
    else {
        theta.value()[var] = x;
        return theta;
    }
    // TODO implement occur check
}
