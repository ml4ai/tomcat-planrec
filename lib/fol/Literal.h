#pragma once

#include "Predicate.h"
#include <vector>
#include "../Visitor.h"

namespace fol {
    template <class T>
    struct Literal {
        Predicate predicate;
        std::vector<T> args;
        bool is_negative=false;

        // operator for comparing Literals, in the context of unification
    friend bool operator==(const Literal<T> &lhs, const Literal<T> &rhs) {
                bool eq=true;
                for(int i=0; i < lhs.args.size(); i++) {
                    if (boost::apply_visitor(type_visitor(), (lhs.args).at(i)) == "Variable" || boost::apply_visitor(type_visitor(), (rhs.args).at(i)) == "Variable" ) {
                        eq=false; // any variable means they aren't unified
                    }
                    else if (boost::apply_visitor(type_visitor(), (lhs.args).at(i)) != boost::apply_visitor(type_visitor(), (rhs.args).at(i))) {
                        eq=false; // different data types
                    }
                    else if (boost::apply_visitor(type_visitor(), (lhs.args).at(i)) == "Constant") {
                        if (get<Constant>(lhs.args.at(i)).name != get<Constant>(rhs.args.at(i)).name) {
                            eq = false; // both entities but different ones
                        }
                    }
                    else if (boost::apply_visitor(type_visitor(), (lhs.args).at(i)) == "Predicate") {
                        if (get<Function>(lhs.args.at(i)).name != get<Function>(rhs.args.at(i)).name) {
                            eq = false; // both predictes but different ones
                        }
                        // else recursively run the arguments through again
                        else {
                            Literal x;
                            Literal y;
                            x.predicate = get<Function>((lhs.args).at(i)).name;
                            x.args = get<Function>((lhs.args).at(i)).args;
                            y.predicate = get<Function>((rhs.args).at(i)).name;
                            y.args = get<Function>((rhs.args).at(i)).args;
                            eq = (x == y);                            
                        }
                    }

                }
                return eq; // add condition where each element are equal
            }
    };
}
