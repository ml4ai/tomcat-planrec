// This is the unification c++ algorithm

// add in the new data structs for the algorithm

// should make a cmake file for this

#include <iostream>
#include <vector>
#include <stack>
#include <queue>
#include <algorithm>
#include <variant>
#include <unordered_map>
#include "boost/variant.hpp"
#include "Symbol.h" // base object
#include "Variable.h" // variable inherited from symbol
#include "Constant.h" // constant inherited from symbol
#include "Term.h" // vector of variables, constants, functions
#include "Function.h" // predicate, args are terms
#include "Literal.h" // negatable predicate
#include "Visitor.h" // for type checking

using namespace std;

// setting up unordered_map for our substitution list
typedef unordered_map<string, string> sub_list_type;
using sub_list = sub_list_type;

// now for the substition formula for replacing the variable in an atom/predicate
void substitute(Literal &x, Literal &y, sub_list &z, int ix) {
    if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Variable") {
        // write the substitution to z
        z[get<Variable>((x.args).at(ix)).name] = get<Variable>((y.args).at(ix)).name;
        // insert the new subbed element and then erase the old one
        (x.args).insert(x.args.begin() + ix, get<Variable>((y.args).at(ix)));
        ix++;
        (x.args).erase(x.args.begin() + ix);
    }
    else if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Constant") {
        // write substitution to z
        z[get<Variable>((x.args).at(ix)).name] = get<Constant>((y.args).at(ix)).name;
        // insert substitution and then erase the old entry
        (x.args).insert(x.args.begin() + ix, get<Constant>((y.args).at(ix)));
        ix++;
        (x.args).erase(x.args.begin() + ix);
    }
    else if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Predicate") {
        // write substitution to z
        z[get<Variable>((x.args).at(ix)).name] = get<Function>((y.args).at(ix)).name;
        // insert substitution and then erase the old entry
        (x.args).insert(x.args.begin() + ix, get<Function>((y.args).at(ix)));
        ix++;
        (x.args).erase(x.args.begin() + ix);
    }
}

// now we apply the unification algorithm on the predicate pairs
sub_list unification(Literal x, Literal y, sub_list z) {
        
    // make sure number of arguments of each expression are the same
    if ((x.args).size() != (y.args).size()) {
        z.clear();
        return z; // need to make it return the substitution list with a fail
    }
    // check for unification
    if (x == y) {
        return z;
    }
    for(int ix=0; ix < (x.args).size(); ix++) {
    // if variable is explicit in x expression
        if (boost::apply_visitor(type_visitor(), x.args.at(ix)) == "Variable") {
            // substitute x for y
            substitute(x, y, z, ix);
            return unification(x, y, z);
        }
        // if variable is explicit in y expression
        else if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Variable") {
            // substitute y for x
            substitute(y, x, z, ix);
            return unification(x, y, z);
        }
        // if they are predicates and thus the variable is implicit (hopefully)
        else if (boost::apply_visitor(type_visitor(), (x.args).at(ix)) == "Predicate" && boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Predicate") {
            // if the arguments are predicates we run them through the unification algorithm again
            // here we now have to construct a Literal data type from the function data type argument of a previous literal to then pass back into the 
            // unification algoirthm 
            Literal x1;
            Literal y1;
            x1.predicate = get<Function>((x.args).at(ix)).name;
            x1.args = get<Function>((x.args).at(ix)).args;
            y1.predicate = get<Function>((y.args).at(ix)).name;
            y1.args = get<Function>((y.args).at(ix)).args;
            return unification(x1, y1, z);
            }
    }
    
}

