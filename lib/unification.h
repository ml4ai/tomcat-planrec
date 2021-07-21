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
using Substitution = std::unordered_map<std::string, Term>;

using Input = boost::variant<Variable, Constant, vector<Term>, Literal<Term>>;

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

Substitution unify(Input x, Input y, Substitution theta) {
    if (boost::apply_visitor(EqualityChecker(), x, y)) {
        return theta;
    }
    else if (x.type() == typeid(Variable)) {
        return unify_var(x, y, theta);
    }
}

Substitution unify_var(Variable var, Input x, Substitution theta) {

}
