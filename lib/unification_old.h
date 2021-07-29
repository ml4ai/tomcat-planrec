#pragma once
// This is the unification c++ algorithm

#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <variant>
#include <unordered_map>
#include "boost/variant.hpp"
#include "fol/Symbol.h" // base object
#include "fol/Variable.h" // variable inherited from symbol
#include "fol/Constant.h" // constant inherited from symbol
#include "fol/Term.h" // vector of variables, constants, functions
#include "fol/Function.h" // used as predicate, args are terms
#include "fol/Literal.h" // negatable predicate
#include "fol/Predicate.h" //predicate class, used as "label" of literal
#include "Visitor.h" // for type checking

using namespace std;
using namespace fol;

// setting up unordered_map for our substitution list
typedef unordered_map<string, Term> sub_list_type;
using sub_list = variant<sub_list_type, string>;

// now for the substition formula for replacing the variable in an atom/predicate
void substitute(Literal<Term> &x, Literal<Term> &y, sub_list &z, int ix) {
    if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Variable") {
        // write the substitution to z
        get<sub_list_type>(z)[get<Variable>((x.args).at(ix)).name] = get<Variable>((y.args).at(ix));
        // insert the new subbed element and then erase the old one
        (x.args).insert(x.args.begin() + ix, get<Variable>((y.args).at(ix)));
        ix++;
        (x.args).erase(x.args.begin() + ix);
    }
    else if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Constant") {
        // write substitution to z
        get<sub_list_type>(z)[get<Variable>((x.args).at(ix)).name] = get<Constant>((y.args).at(ix));
        // insert substitution and then erase the old entry
        (x.args).insert(x.args.begin() + ix, get<Constant>((y.args).at(ix)));
        ix++;
        (x.args).erase(x.args.begin() + ix);
    }
    else if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Predicate") {
        // write substitution to z
        get<sub_list_type>(z)[get<Variable>((x.args).at(ix)).name] = get<Function>((y.args).at(ix));
        // insert substitution and then erase the old entry
        (x.args).insert(x.args.begin() + ix, get<Function>((y.args).at(ix)));
        ix++;
        (x.args).erase(x.args.begin() + ix);
    }
}

// now we apply the unification algorithm on the predicate pairs
sub_list unify(Literal<Term> x, Literal<Term> y, sub_list z) {
        
    // make sure number of arguments of each expression are the same
    if ((x.args).size() != (y.args).size()) {
        z = "Error: Predicates have different numbers of arguments. Unification not possible.";
        return z; // need to make it return the substitution list with a fail
    }
    // check for unification
    // heavy lifting here is done in the added operator in the literal definition
    if (x == y) {
        return z;
    }
    for(int ix=0; ix < (x.args).size(); ix++) {
        // if variable is explicit in x expression
        if (boost::apply_visitor(type_visitor(), x.args.at(ix)) == "Variable") {
            // substitute x for y
            substitute(x, y, z, ix);
            return unify(x, y, z);
        }
        // if variable is explicit in y expression
        else if (boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Variable") {
            // substitute y for x
            substitute(y, x, z, ix);
            return unify(x, y, z);
        }
        // if they are predicates and thus the variable is implicit (hopefully)
        else if (boost::apply_visitor(type_visitor(), (x.args).at(ix)) == "Predicate" && boost::apply_visitor(type_visitor(), (y.args).at(ix)) == "Predicate") {
            // if the arguments are predicates we run them through the unification algorithm again
            // here we now have to construct a Literal data type from the function data type argument of a previous literal to then pass back into the 
            // unification algoirthm 
            Literal<Term> x1;
            Literal<Term> y1;
            Predicate p1 = get<Function>((x.args).at(ix)).name;
            Predicate q1 = get<Function>((y.args).at(ix)).name;
            x1.predicate = p1;
            x1.args = get<Function>((x.args).at(ix)).args;
            y1.predicate = q1;
            y1.args = get<Function>((y.args).at(ix)).args;
            
            // the unification function doesnt do the replacements outside the scope of the function, perhaps I remove this argument since its already
            // unified so it doesn't impact the checker? 
            sub_list z1;
            z1 = unify(x1, y1, z1);
            // merge z1 and z, since unification could have failed z1 could have a fail condition passed along too
            // concerned 
            if (holds_alternative<string>(z1)) {
                return z1;
            }
            else {
                get<sub_list_type>(z).insert(get<sub_list_type>(z1).begin(), get<sub_list_type>(z1).end());
            }
            // remove the argument
            x.args.erase(x.args.begin() + ix);
            y.args.erase(y.args.begin() + ix);

            return unify(x, y, z);
            }
    }
    // if unification algorithm can't sub these literal then it has failed / unification isn't possible
    if (!(x == y)) {
        sub_list z_s; // need to create a new variant sub_list incase it has already had a sub_list_type filled in
        z_s = "Error: Constants or Predicates do not match. Unification is not possible.";
        return z_s;
    }
    
}

