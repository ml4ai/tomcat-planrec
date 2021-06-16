// This is the unification c++ algorithm

// To Do:
    // add literals and clauses to KB (knowledge engine stuff)
    // confer about predicate class in ast
    // unification and overloads in subs left

#include <iostream>
#include <vector>
#include <stack>
#include <queue>
#include <algorithm>
#include <variant>
#include <unordered_map>
#include "boost/variant.hpp"
#include "ast.hpp"

using namespace std;

// client::ast::Entity // constants
// client::ast::Variable // variable
// client::ast::AtomicFormula // predicate however a little too restrictive right now for the recursion I need I think

class KnowledgeBase {
    public:
    // define our data types, we use our own predicate and the boost::variant for recursion purposes
    struct Predicate;
    struct Uni_Variable : client::ast::Variable {
        public:
        bool replaced = false;
    };
    typedef boost::variant< client::ast::Entity, Uni_Variable, Predicate > argument; // only boost::variant allows for recursion
    typedef vector<argument> v_args;


    // a structure for predicate data types, recursive
    struct Predicate {
        public:
            string name;
            v_args args;

            // constructor
            Predicate(string x, v_args y) {
                name = x;
                args = y; 
        }
    };

    // setting up unordered_map for our substitution list
    typedef unordered_map<string, string> sub_list;

    // this function below will return Term type as a string via overloading and vister methods
    class my_visitor : public boost::static_visitor<string>
    {
    public:
        string operator()(client::ast::Entity x) const {
            return "Entity";
        }
        string operator()(Uni_Variable x) const {
            return "Variable";
        }
        string operator()(Predicate x) const {
            return "Predicate";
        }
    };

    // now for the substition formula for replacing the variable in an atom/predicate, 
    // make sure its a global change
    // needs to know the object type at compile-time
    void substitute(Uni_Variable &x, v_args &y, sub_list &z, int i) {
        if (boost::apply_visitor(my_visitor(), y[i]) == "Variable") {
            x.name = get<Uni_Variable>(y[i]).name;
            x.replaced = true;
            z[x.name] = get<Uni_Variable>(y[i]).name;
        }
        else if (boost::apply_visitor(my_visitor(), y[i]) == "Entity") {
            x.name = get<client::ast::Entity>(y[i]).name;
            x.replaced = true;
            z[x.name] = get<client::ast::Entity>(y[i]).name;
        }
        else if (boost::apply_visitor(my_visitor(), y[i]) == "Predicate") {
            x.name =  get<Predicate>(y[i]).name;
            x.replaced = true;
            z[x.name] = get<Predicate>(y[i]).name;
        }

    }

    // now we apply the unification algorithm on the predicate pairs
    sub_list unification(Predicate &x, Predicate &y, sub_list &z) {
        
        // make sure number of arguments of each expression are the same
        if (x.args.size() != y.args.size()) {
            z.clear();
            return z; // need to make it return the substitution list with a fail
        }

        // if already unified, algorithm is complete, make sure comparision of objects works in c++ conditionals
        // need to update this, cause of final errors, if define == for these objects it might work
        // rewrite to just check all the names
        // check for unification
        bool unified=true;
        for(int i=0; i < x.args.size(); i++) {
            if (boost::apply_visitor(my_visitor(), x.args[i]) == "Variable") {
                if (get<Uni_Variable>(x.args[i]).replaced == false){
                    unified = false;
                }
            }
            else if (boost::apply_visitor(my_visitor(), y.args[i]) == "Variable" ) {
                if (get<Uni_Variable>(y.args[i]).replaced == false){
                    unified = false;
                }
            }
            else if (boost::apply_visitor(my_visitor(), x.args[i]) == "Entity" && boost::apply_visitor(my_visitor(), y.args[i])== "Entity") {
                    if (get<client::ast::Entity>(x.args[i]).name != get<client::ast::Entity>(y.args[i]).name) {
                        unified = false;
                        return z;
                    }
            }
            else if (boost::apply_visitor(my_visitor(), x.args[i]) == "Predicate" && boost::apply_visitor(my_visitor(), y.args[i])== "Predicate") {
                    if (get<Predicate>(x.args[i]).name != get<Predicate>(y.args[i]).name) {
                        unified = false;
                        return z;
                    }
            }            
        }
        if (unified == true) {
            return z;
        }
        // now if we have only 1 argument
        else if (x.args.size() == 1) {
            // if variable is explicit in x expression
            if (boost::apply_visitor(my_visitor(), x.args[0]) == "Variable" && get<Uni_Variable>(x.args[0]).replaced == false) {
                // substitute x for y
                substitute(get<Uni_Variable>(x.args[0]), y.args, z, 0);
                return unification(x, y, z);
            }
            // if variable is explicit in y expression
            else if (boost::apply_visitor(my_visitor(), y.args[0]) == "Variable" && get<Uni_Variable>(y.args[0]).replaced == false) {
                // substitute y for x
                substitute(get<Uni_Variable>(y.args[0]), x.args, z, 0);
                return unification(x, y, z);
            }
            // if they are predicates and thus the variable is implicit (hopefully)
            else if (boost::apply_visitor(my_visitor(), x.args[0]) == "Predicate" && boost::apply_visitor(my_visitor(), y.args[0]) == "Predicate") {
                // if the arguments are predicates we run them through the unification algorithm again
                return unification(get<Predicate>(x.args[0]), get<Predicate>(y.args[0]), z);
                }
        }

        // now for multiple arguments, we will iterate through them and send each one through the function
        else if (x.args.size() > 1) {
            for(int i=0; i < x.args.size(); i++) {
                // we now need to ignore the already unified statements, if unified their names will be the same
                if (boost::apply_visitor(my_visitor(), x.args[i]) == "Variable" && get<Uni_Variable>(x.args[i]).replaced == false) {
                        // substitute x for y
                        substitute(get<Uni_Variable>(x.args[i]), y.args, z, i);
                        return unification(x, y, z);
                }
                else if (boost::apply_visitor(my_visitor(), y.args[i]) == "Variable" && get<Uni_Variable>(y.args[0]).replaced == false) {
                        // substitute y for x
                        substitute(get<Uni_Variable>(y.args[i]), x.args, z, i);
                        return unification(x, y, z);
                }
                else if (boost::apply_visitor(my_visitor(), x.args[i]) == "Predicate" && boost::apply_visitor(my_visitor(), y.args[i]) == "Predicate") {
                        // run arguments of predicates through function 
                        return unification(get<Predicate>(x.args[i]), get<Predicate>(y.args[i]), z);
                    }
            }
        }
    }
};

int main() {

    // sample predicates for testing unification
    typedef boost::variant<client::ast::Entity, KnowledgeBase::Uni_Variable, KnowledgeBase::Predicate> argument; // only boost::variant allows for recursion
    typedef vector<argument> v_args;

    client::ast::Entity John("John");

    client::ast::Entity Richard("Richard");

    KnowledgeBase::Uni_Variable X;

    X.name = "X";

    argument J1=John;
    argument R1=Richard;
    argument X1=X;

    v_args v1;
    v1.push_back(J1);
    v1.push_back(R1);
    v_args v2;
    v2.push_back(J1);
    v2.push_back(X1);

    KnowledgeBase::Predicate P1("Knows", v1);
    KnowledgeBase::Predicate P2("Knows", v2);

    // setting up to run unification 
    typedef unordered_map<string, string> subs;
    subs s1;

    KnowledgeBase Obj;

    s1 = Obj.unification(P1, P2, s1);

    // cout << s1;
    

}
