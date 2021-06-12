// This is the unification c++ algorithm

// To Do:
    // add literals and clauses to KB (knowledge engine stuff)
    // confer about predicate class in ast

#include <iostream>
#include <vector>
#include <stack>
#include <queue>
#include <algorithm>
#include <variant>
#include "boost/variant.hpp"
#include "ast.hpp"

using namespace std;

// client::ast::Entity // constants
// client::ast::Variable // variable
// client::ast::AtomicFormula // predicate however a little to restrictive right now for the recursion I need I think

class KnowledgeBase {

    // define our data types, we use our own predicate and the boost::variant for recursion purposes
    struct Predicate;
    typedef boost::variant<client::ast::Entity, client::ast::Variable, Predicate> argument; // only boost::variant allows for recursion
    typedef vector<argument> v_args;


    // a structure for predicate data types, recursive
    struct Predicate {
        public:
            string name;
            v_args args;

            // constructor
            predicate(string x, v_args y) {
                name = x;
                args = y; 
        }
    };

    // setting up unordered_map for our substitution list
    typedef unordered_map<string, string> sub_list;

    // this function below will return Term type as a string via overloading
    string type_check(client::ast::Entity x) {
        return "Entity";
    }
    string type_check(client::ast::Variable x) {
        return "Variable";
    }
    string type_check(Predicate x) {
        return "Predicate";
    }

    // now for the substition formula for replacing the variable in an atom/predicate
    void substitute(Variable x, argument y, sub_list z) {
        x = y;
        z[x.name] = z[y.name];
    }

    // now we apply the unification algorithm on the predicate pairs
    sub_list unification(Predicate x, Predicate y, sub_list z) {
        
        // make sure number of arguments of each expression are the same
        if (x.args.size() != y.args.size()) {
            z.clear();
            return z; // need to make it return the substitution list with a fail
        }

        // if already unified, algorithm is complete, make sure comparision of objects works in c++ conditionals
        else if (x.args == y.args) {
            return z;
        }
        // now if we have only 1 argument
        else if (x.args.size() == 1) {
            // if variable is explicit in x expression
            if (type_check(x.args[0]) == "Variable") {
                // substitute x for y
                substitute(x.args[0], y.args[0], z);
                return unification(x, y, z);
            }
            // if variable is explicit in y expression
            else if (type_check(y.args[0]) == "Variable") {
                // substitute y for x
                substitute(y.args[0], x.args[0], z);
                return unification(x, y, z);
            }
            // if they are predicates and thus the variable is implicit (hopefully)
            else if (type_check(x.args[0]) == "Predicate" && type_check(y.args[0]) == "Predicate") {
                // if the arguments are predicates we run them through the unification algorithm again
                return unification(x.args[0], y.args[0], z);
                }
            }
            else if (type_check(x.args[0]) == "Entity" && type_check(y.args[0]) == "Entity") {
                // in this case there is no variable so unification is not possible
                z.clear();
                return z;
            }
        }
        // now for multiple arguments, we will iterate through them and send each one through the function
        else if (x.args.size() > 1) {
            for(int i=0; i < x.args.size(); i++) {
                // we now need to ignore the already unified statements, if unified their names will be the same
                if (x.args[i].name != y.args[i].name) { 
                    if (type_check(x.args[i]) == "Variable") {
                        // substitute x for y
                        substitute(x.args[i], y.args[i], z);
                        return unification(x, y, z);
                    }
                    else if (type_check(y.args[i]) == "Variable") {
                        // substitute y for x
                        substitute(y.args[i], x.args[i], z);
                        return unification(x, y, z);
                    }
                    else if (type_check(x.args[i]) == "Predicate" && type_check(y.args[i]) == "Predicate") {
                        // run arguments of predicates through function 
                        return unification(x.args[i], y.args[i], z);
                    }
                    else if (type_check(x.args[i]) == "Entity" && type_check(y.args[i]) == "Entity") {
                        // if 2 constants that are not equal are in the expresison, unification is not possible
                        z.clear();
                        return z;
                    }
                }
            }
        }
    }
};