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
    // still have recursive issues
    struct Predicate;
    typedef boost::variant< client::ast::Entity, client::ast::Variable, Predicate > argument; // only boost::variant allows for recursion
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
            // this requires names to be unique, database semantics
            friend bool operator==(const Predicate &lhs, const Predicate &rhs) {
                bool eq=true;
                for(int i=0; i < lhs.args.size(); i++) {
                    if (boost::apply_visitor(my_visitor(), (lhs.args).at(i)) == "Variable" || boost::apply_visitor(my_visitor(), (rhs.args).at(i)) == "Variable" ) {
                        eq=false; // any variable means they aren't unified
                    }
                    else if (boost::apply_visitor(my_visitor(), (lhs.args).at(i)) != boost::apply_visitor(my_visitor(), (rhs.args).at(i))) {
                        eq=false; // different data types
                    }
                    else if (boost::apply_visitor(my_visitor(), (lhs.args).at(i)) == "Entity") {
                        if (get<client::ast::Entity>(lhs.args.at(i)).name != get<client::ast::Entity>(rhs.args.at(i)).name) {
                            eq = false; // both entities but different ones
                        }
                    }
                    else if (boost::apply_visitor(my_visitor(), (lhs.args).at(i)) == "Predicate") {
                        if (get<Predicate>(lhs.args.at(i)).name != get<Predicate>(rhs.args.at(i)).name) {
                            eq = false; // both predictes but different ones
                        }
                    }                    
                }
                return eq; // add condition where each element are equal
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
        string operator()(client::ast::Variable x) const {
            return "Variable";
        }
        string operator()(Predicate x) const {
            return "Predicate";
        }
    };

    // now for the substition formula for replacing the variable in an atom/predicate
    void substitute(Predicate x, Predicate y, sub_list z, int ix) {
        if (boost::apply_visitor(my_visitor(), (y.args).at(ix)) == "Variable") {
            // write the substitution to z
            z[get<client::ast::Variable>((x.args).at(ix)).name] = get<client::ast::Variable>((y.args).at(ix)).name;
            // insert the new subbed element and then erase the old one
            (x.args).insert(x.args.begin() + ix, get<client::ast::Variable>((y.args).at(ix)));
            ix++;
            (x.args).erase(x.args.begin() + ix);
        }
        else if (boost::apply_visitor(my_visitor(), (y.args).at(ix)) == "Entity") {
            // write substitution to z
            z[get<client::ast::Variable>((x.args).at(ix)).name] = get<client::ast::Entity>((y.args).at(ix)).name;
            // insert substitution and then erase the old entry
            (x.args).insert(x.args.begin() + ix, get<client::ast::Entity>((y.args).at(ix)));
            ix++;
            (x.args).erase(x.args.begin() + ix);
        }
        else if (boost::apply_visitor(my_visitor(), (y.args).at(ix)) == "Predicate") {
            // write substitution to z
            z[get<client::ast::Variable>((x.args).at(ix)).name] = get<Predicate>((y.args).at(ix)).name;
            // insert substitution and then erase the old entry
            (x.args).insert(x.args.begin() + ix, get<Predicate>((y.args).at(ix)));
            ix++;
            (x.args).erase(x.args.begin() + ix);
        }

    }

    // now we apply the unification algorithm on the predicate pairs
    sub_list unification(Predicate x, Predicate y, sub_list z) {
        
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
            if (boost::apply_visitor(my_visitor(), x.args.at(ix)) == "Variable") {
                // substitute x for y
                substitute(x, y, z, ix);
                return unification(x, y, z);
            }
            // if variable is explicit in y expression
            else if (boost::apply_visitor(my_visitor(), (y.args).at(ix)) == "Variable") {
                // substitute y for x
                substitute(y, x, z, ix);
                return unification(x, y, z);
            }
            // if they are predicates and thus the variable is implicit (hopefully)
            else if (boost::apply_visitor(my_visitor(), (x.args).at(ix)) == "Predicate" && boost::apply_visitor(my_visitor(), (y.args).at(ix)) == "Predicate") {
                // if the arguments are predicates we run them through the unification algorithm again
                return unification(get<Predicate>((x.args).at(ix)), get<Predicate>((y.args).at(ix)), z);
                }
        }
    }
};

int main() {

    // sample predicates for testing unification
    typedef boost::variant<client::ast::Entity, client::ast::Variable, KnowledgeBase::Predicate> argument; // only boost::variant allows for recursion
    typedef vector<argument> v_args;

    client::ast::Entity John("John");

    client::ast::Entity Richard("Richard");

    client::ast::Variable X("X");

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
