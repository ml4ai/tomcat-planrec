#pragma once

#include "Hash.h"
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

template <typename T> constexpr auto type_name() noexcept {
    std::string_view name = "Error: unsupported compiler", prefix, suffix;
#ifdef __clang__
    name = __PRETTY_FUNCTION__;
    prefix = "auto type_name() [T = ";
    suffix = "]";
#elif defined(__GNUC__)
    name = __PRETTY_FUNCTION__;
    prefix = "constexpr auto type_name() [with T = ";
    suffix = "]";
#elif defined(_MSC_VER)
    name = __FUNCSIG__;
    prefix = "auto __cdecl type_name<";
    suffix = ">(void) noexcept";
#endif
    name.remove_prefix(prefix.size());
    name.remove_suffix(suffix.size());
    return name;
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

template <class T> std::string type(T x) {
    return boost::apply_visitor(GetType(), x);
}

struct EqualityChecker : public boost::static_visitor<bool> {
    template <typename T, typename U>
    bool operator()(const T& lhs, const U& rhs) const {
        return false;
    }
    template <typename T> bool operator()(const T& lhs, const T& rhs) const {
        return lhs == rhs;
    }
    //bool operator()(const Term& lhs, const Term& rhs) const {
        //return boost::apply_visitor(EqualityChecker(), lhs, rhs);
    //}
};

std::optional<Substitution>
unify_var(Variable v, Input i, std::optional<Substitution>& s);

std::optional<Substitution>
unify(Input x, Input y, std::optional<Substitution> theta);

struct TermUnifier : public boost::static_visitor<> {
    std::optional<Substitution> theta;

    TermUnifier(std::optional<Substitution> theta) : theta(theta) {}

    template<class T, class U>
    void operator()(const T& lhs, const U& rhs) {
        this->theta = unify(lhs, rhs, this->theta);
    }
};

std::optional<Substitution>
unify(Input x, Input y, std::optional<Substitution> theta) {
    using boost::get;
    //std::cout << "x: " << x << " type: " << type(x) << std::endl;
    //std::cout << "y: " << y << " type: " << type(y) << std::endl;

    if (theta == nullopt) {
        return nullopt;
    }
    else if (boost::apply_visitor(EqualityChecker(), x, y)) {
        return theta;
    }
    else if (type(x) == type(y) && type(x) =="Term") {
        auto visitor = TermUnifier(theta);
        boost::apply_visitor(visitor, get<Term>(x), get<Term>(y));
        return visitor.theta;
    }
    else if (type(x) == "Variable") {
        return unify_var(get<Variable>(x), y, theta);
    }
    else if (type(y) == "Variable") {
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

        // If the size of the vectors is not the same, return failure.
        if (x_vec.size() != y_vec.size()) {
            return std::nullopt;
        }

        if (x_vec.size() == 1) {
            return unify(x_vec.at(0), y_vec.at(0), theta);
        }
        else {
            auto x_rest = vector<Term>();
            auto y_rest = vector<Term>();
            for (int i = 1; i < x_vec.size(); i++) {
                x_rest.push_back(x_vec.at(i));
            }
            for (int i = 1; i < y_vec.size(); i++) {
                y_rest.push_back(y_vec.at(i));
            }
            return unify(
                x_rest, y_rest, unify(x_vec.at(0), y_vec.at(0), theta));
        }
    }
    else {
        return nullopt;
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
    else {
        theta.value().insert_or_assign(var, x);
        return theta;
    }
    // TODO implement occur check
}
