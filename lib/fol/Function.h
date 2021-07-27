#pragma once

#include "Term.h"

namespace fol {
    struct Function {
        std::string name;
        std::vector<Term> args = {};
        friend bool operator==(const Function& lhs, const Function& rhs) {
            return (lhs.name == rhs.name) && (lhs.args == rhs.args);
        }
        friend std::ostream& operator<<(std::ostream& out, const Function& f) {
            out << "(";
            out << f.name;
            for (int i = 0; i < f.args.size(); i++) {
                out << f.args.at(i);
                if (i < f.args.size()) {
                    out << " ";
                }
            }
            out << ")";
            return out;
        };
    };
} // namespace fol
