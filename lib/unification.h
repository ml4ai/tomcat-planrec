#pragma once

#include "Hash.h"
#include "util/boost_variant_helpers.h"
#include <boost/log/trivial.hpp>
#include <boost/variant.hpp>
#include <fol/Constant.h>
#include <fol/Literal.h>
#include <fol/Term.h>
#include <fol/Variable.h>
#include <optional>
#include <string_view>
#include <unordered_map>

using namespace fol;
using namespace std;

string head(Literal<Term> x) { return x.predicate; }

string head(Function x) { return x.name; }

template <class T> T head(vector<T> vec) { return vec.at(0); }

template <class T> vector<Term> tail(T expr) { return expr.args; }

template <class T> vector<T> tail(vector<T> vec) {
    vector<T> rest = {};
    for (int i = 1; i < vec.size(); i++) {
        rest.push_back(vec.at(i));
    }
    return rest;
}

using Input = boost::variant<Variable,
                             Constant,
                             Function,
                             Term,
                             Predicate,
                             vector<Term>,
                             Literal<Term>>;

using Substitution = std::unordered_map<Variable, Input, Hash<Variable>>;

struct GetType : public boost::static_visitor<std::string> {
    std::string operator()(const Variable& x) const { return "Variable"; }
    std::string operator()(const Constant& x) const { return "Constant"; }
    std::string operator()(const Function& x) const { return "Function"; }
    std::string operator()(const Term& x) const { return "Term"; }
    std::string operator()(const Predicate& x) const { return "Predicate"; }
    std::string operator()(const vector<Term>& x) const {
        return "vector<Term>";
    }
    std::string operator()(const Literal<Term>& x) const {
        return "Literal<Term>";
    }
};

struct EqualityChecker : public boost::static_visitor<bool> {
    template <typename T, typename U>
    bool operator()(const T& lhs, const U& rhs) const {
        return false;
    }
    template <typename T> bool operator()(const T& lhs, const T& rhs) const {
        return lhs == rhs;
    }
    template <class T> bool operator()(const Input& lhs, const T& rhs) const {
        return apply_visitor(*this, lhs, static_cast<Input>(rhs));
    }
};

std::optional<Substitution>
unify_var(Variable v, Input i, std::optional<Substitution>& s);

std::optional<Substitution>
unify(Input x, Input y, std::optional<Substitution> theta);

struct TermUnifier : public boost::static_visitor<> {
    std::optional<Substitution> theta;

    TermUnifier(std::optional<Substitution> theta) : theta(theta) {}

    template <class T, class U> void operator()(const T& lhs, const U& rhs) {
        this->theta = unify(lhs, rhs, this->theta);
    }
};

template <class T, class U> auto unify_compound_expr(T x, T y, U theta) {
    return unify(tail(x), tail(y), unify(head(x), head(y), theta));
}

std::optional<Substitution>
unify(Input x, Input y, std::optional<Substitution> theta) {
    using boost::get;

    if (theta == nullopt) {
        return nullopt;
    }
    else if (visit<EqualityChecker>(x, y)) {
        return theta;
    }
    else if (visit<GetType>(x) == visit<GetType>(y) &&
             visit<GetType>(x) == "Term") {
        auto visitor = TermUnifier(theta);
        boost::apply_visitor(visitor, get<Term>(x), get<Term>(y));
        return visitor.theta;
    }
    else if (visit<GetType>(x) == "Variable") {
        return unify_var(get<Variable>(x), y, theta);
    }
    else if (visit<GetType>(y) == "Variable") {
        return unify_var(get<Variable>(y), x, theta);
    }

    else if (x.type() == typeid(Literal<Term>) &&
             y.type() == typeid(Literal<Term>)) {
        auto x_expr = get<Literal<Term>>(x);
        auto y_expr = get<Literal<Term>>(y);
        return unify_compound_expr(x_expr, y_expr, theta);
    }
    else if (x.type() == typeid(Function) && y.type() == typeid(Function)) {
        auto x_expr = get<Function>(x);
        auto y_expr = get<Function>(y);
        return unify_compound_expr(x_expr, y_expr, theta);
    }

    else if (x.type() == typeid(vector<Term>) &&
             y.type() == typeid(vector<Term>)) {
        auto x_vec = get<vector<Term>>(x);
        auto y_vec = get<vector<Term>>(y);

        // If the size of the vectors is not the same, return failure.
        if (x_vec.size() != y_vec.size()) {
            return std::nullopt;
        }

        if (x_vec.size() == 1) {
            return unify(head(x_vec), head(y_vec), theta);
        }
        else {
            return unify(tail(x_vec),
                         tail(y_vec),
                         unify(head(x_vec), head(y_vec), theta));
        }
    }
    else {
        return nullopt;
    }
}

bool occur_check(Substitution theta, Variable var, Input x) {
    // TODO - Implement this!
    if (visit<EqualityChecker>(static_cast<Input>(var), x)) {
        return true;
    }
    else if (x.type() == typeid(Variable) && theta.contains(get<Variable>(x))) {
        return occur_check(theta, var, theta.at(get<Variable>(x)));
    }
    else if (x.type() == typeid(Function)) {
        for (Term term : get<Function>(x).args) {
            if (occur_check(theta, var, term)) {
                return true;
            }
        }
    }
    else if (x.type() == typeid(Literal<Term>)) {
        for (Term term : get<Literal<Term>>(x).args) {
            if (occur_check(theta, var, term)) {
                return true;
            }
        }
    }
    else {
        return false;
    }
}

std::optional<Substitution> unify(Input x, Input y) {
    return unify(x, y, Substitution());
}

std::optional<Substitution>
unify_var(Variable var, Input x, std::optional<Substitution>& theta) {
    if (theta.value().contains(var)) {
        auto val = theta.value().at(var);
        return unify(val, x, theta);
    }
    else if (x.type() == typeid(Variable) &&
             theta.value().contains(boost::get<Variable>(x))) {
        auto x_var = boost::get<Variable>(x);
        auto val = theta.value().at(x_var);
        return unify(var, val, theta);
    }
    // NOTE occur check function has not been implemented fully! 
    else if (occur_check(theta.value(), var, x)){
        return nullopt;
    }
    else {
        theta.value().insert_or_assign(var, x);
        return theta;
    }
}
