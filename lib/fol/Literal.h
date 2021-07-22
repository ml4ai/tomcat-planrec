#pragma once

#include "../Visitor.h"
#include "Predicate.h"
#include <vector>

namespace fol {
    template <class T> struct Literal {
        Predicate predicate;
        std::vector<T> args;
        bool is_negative = false;

        // operator for comparing Literals, in the context of unification
        friend bool operator==(const Literal<T>& lhs, const Literal<T>& rhs) {
            return (lhs.predicate == rhs.predicate) && (lhs.args == rhs.args);
        }

        friend std::ostream& operator<<(std::ostream& out,
                                        const Literal<T>& lit) {
            out << "Literal(";
            out << "Predicate(" << lit.predicate << ") ";
            for (int i=0; i < lit.args.size(); i++) {
                out << lit.args.at(i);
                if (i < lit.args.size() - 1) {
                    out << " ";
                }
            }
            out << ")";
            return out;
        };
    };
} // namespace fol
