#pragma once

#include "Clause.h"
#include "fol/Literal.h"
#include "fol/Predicate.h"
#include "fol/Term.h"
#include "util.h"
#include "parsing/ast.hpp"
#include "CNF.h"
#include <iostream>
#include <string>
#include <tuple>
#include <variant>
#include <vector>


using namespace std;
using namespace fol;

// base data structs of the knowledge base to be populated using tell()
struct KnowledgeBase {
    vector<ast::Sentence> sentences; // this should be changed to the data type of CNF sentences 
    vector<Clause> clauses;
    vector<Clause> definite_clauses;
    // should the facts be indexed/mapped?
    vector<Literal<Term>> facts;

};

// should this be a method in the KB or of the clause struct?
// this method returns whether clause is definite or not, namely, if there is only exactly one positive literal.
bool isDefiniteClause(Clause c) {
    Literal<Term> lit;
    int i=0;
    for (auto lit : c.literals) {
        if (!lit.is_negative) {
            i+=1;
        }
    }
    if (i == 1) {
        return true;
    }
    else {
        return false;
    }
}

void tell(KnowledgeBase& kb, ast::Sentence sentence) {
    // need to add CNF converter to run on the sentence first
    ast::CNF cnf_tell = ast::to_CNF(sentence);

    kb.sentences.push_back(sentence); // store original sentence

    for (Clause c : cnf_tell.conjunctionOfClauses) {
        kb.clauses.push_back(c);
    }
}; 

void tell(KnowledgeBase& kb, Literal<Term> lit_in) {
    // add literal to knowledge base as a fact
    kb.facts.push_back(lit_in);
};

// This is part of my permutation algorithm for permuting the literals to get CNF from DNF
// check this out again
// c1 should get appended by each literal in c2, making c2.literals.size() number of output clauses
// example: c1: [a, b] | c2: [d,e] then output: [[a,d],[a,e], [b,d], [b,e]]
ast::CNF permute_step(Clause c1, Clause c2) {
    ast::Sentence for_cnf;
    ast::CNF output = ast::construct(for_cnf);
    output.conjunctionOfClauses.clear();
    Clause temp;
    for(Literal<Term> l : c2.literals) {
        temp.literals.insert(temp.literals.begin(), c1.literals.begin(), c1.literals.end());
        temp.literals.push_back(l); // append literal in c2 to c1 
        output.conjunctionOfClauses.push_back(temp); // append that new clause to CNF
        temp.literals.clear(); // reset the clause
    }
    return output;
}


// this method not's a CNF sentence
ast::CNF not_CNF(ast::CNF cnf) {
    // after not'ing the cnf we get a disjunction of conjuctions since all the or's go to and's and vice versa. All the literals are not'd too
    for (Clause c : cnf.conjunctionOfClauses) {
        for (Literal<Term> lit : c.literals) {
            if (lit.is_negative == false) {
                lit.is_negative = true;
            }
            else {
                lit.is_negative = false;
            }
        }
    }
    // after having swapped all the negations, we now interpret cnf as dnf, and clause as a conjuction of literals not disjunction

    // the application of the distribution rule over the disjunctions and conjuctions now results in taking one literal from each "conjuctive-clause"
    // in the dnf sentence and making a clause out of it, and then permuting through all options conjucting each clause, which is a cnf sentence at the end
    // Clause start;
    ast::Sentence for_cnf;
    ast::CNF temp1 = ast::construct(for_cnf);
    temp1.conjunctionOfClauses.clear();
    ast::CNF temp2 = ast::construct(for_cnf); // these are adding clauses, this is the problem
    temp2.conjunctionOfClauses.clear();
    ast::CNF output = ast::construct(for_cnf);
    for (Clause c : cnf.conjunctionOfClauses) {
        for(Clause c1 : output.conjunctionOfClauses) {
            temp1 = permute_step(c1,c);
            temp2.conjunctionOfClauses.insert(temp2.conjunctionOfClauses.end(), temp1.conjunctionOfClauses.begin(), temp1.conjunctionOfClauses.end());
            temp1.conjunctionOfClauses.clear();
        }
        output.conjunctionOfClauses.clear();
        output.conjunctionOfClauses.insert(output.conjunctionOfClauses.end(), temp2.conjunctionOfClauses.begin(), temp2.conjunctionOfClauses.end());
        temp2.conjunctionOfClauses.clear();
    }
    return output;
}

// This will be the ask function for non-variable resolution
// Have an overloaded ask, one that takes a parsed sentence and one that takes CNF sentence
bool ask(KnowledgeBase& kb, ast::Sentence query) {
    // convert the input query into CNF form
    ast::CNF cnf_query = ast::to_CNF(query); // does this convert it to a CNF too?
    // now we not the input, note this causes an expoential increase in the sentence size, do I need a sentence to make CNF's?
    ast::CNF query_clauses = not_CNF(cnf_query);
    // now to start the resolution inference algorithm, this is just checking clauses
    // only need one clause to return empty because then the whole sentence is false, if want to check each clause, ask for each clause

    // first we reduce the query clauses against the facts of the knowledge base
    /* Clause kb_facts;
    for(Literal<Term> l1 : kb.facts) {
        kb_facts.literals.push_back(l1);
        for (Clause c_q : query_clauses.conjunctionOfClauses) {
            cout << "Resolvant size: " << (kb_facts==c_q).literals.size() << "\n"; // this the source of the error, might be failing since input predicates are unary
            if((kb_facts==c_q).literals.size() == 0) { // if we ever get a resolvant that is in contradiction with our kb, the resolution is true
                return true;
            }
            if ((kb_facts==c_q).literals.size() < c_q.literals.size()) { // if the resolvant is smaller than the query, meaning a fact canceled a lit
            // then we replace the old query clause with the resolvant
                c_q.literals.clear();
                c_q.literals.insert(c_q.literals.end(), (kb_facts==c_q).literals.begin(), (kb_facts==c_q).literals.end());
            }
        }
        kb_facts.literals.clear(); // clear for the next literal iteration
    } */
    // now we resolve against the "rules" aka clauses of the KB
    for (Clause c_kb : kb.clauses) {
        for (Clause c_q : query_clauses.conjunctionOfClauses) {
            if((c_kb==c_q).literals.size() == 0) { // if we ever get a resolvant that is in contradiction with our kb, the resolution is true
                return true;
            }
        }
    }
    return false;
}
 // overloaded option for CNF input instead of parsed sentence
bool ask(KnowledgeBase& kb, ast::CNF query) {
    // convert the input query into CNF form
    ast::CNF query_clauses = not_CNF(query);
    // now to start the resolution inference algorithm, this is just checking clauses
    // only need one clause to return empty because then the whole sentence is false, if want to check each clause, ask for each clause

    // first we reduce the query clauses against the facts of the knowledge base
    Clause kb_facts;
    Clause temp_resolve;
    for(Literal<Term> l1 : kb.facts) {
        kb_facts.literals.push_back(l1);
        for (Clause c_q : query_clauses.conjunctionOfClauses) {
            temp_resolve.literals.insert(temp_resolve.literals.end(), (kb_facts==c_q).literals.begin(), (kb_facts==c_q).literals.end());
            if(temp_resolve.literals.size() == 0) { // if we ever get a resolvant that is in contradiction with our kb, the resolution is true
            return true;
            }
            if (temp_resolve.literals.size() < c_q.literals.size()) { // if the resolvant is smaller than the query, meaning a fact canceled a lit
            // then we replace the old query clause with the resolvant
                c_q.literals.clear();
                c_q.literals.insert(c_q.literals.end(), temp_resolve.literals.begin(), temp_resolve.literals.end());
            }
            temp_resolve.literals.clear(); // clear the temp resolution for next loop iteration
        }
        kb_facts.literals.clear(); // clear for the next literal iteration
    }
    // now we resolve against the "rules" aka clauses of the KB
    for (Clause c_kb : kb.clauses) {
        for (Clause c_q : query_clauses.conjunctionOfClauses) {
            if((c_kb==c_q).literals.size() == 0) { // if we ever get a resolvant that is in contradiction with our kb, the resolution is true
                return true;
            }
        }
    }
    return false;
}

// now for the ask_vars method, which will return a substitution list for a variable in the query, if resolute 
// we do not have the standard aparting implemented right now, we are operating on each variable input will have a 
// unqiue name

// unless we restrict ourselves to horn clauses the inputs to the ask_vars will have to be a literal and it will just be unified against the facts
// of the kb. AIMA p.301 for detials.

// really need to test this function
sub_list ask_vars(KnowledgeBase& kb, ast::Literal<Term> query) {    
    sub_list sub;
    sub_list temp;
    for(Literal lit : kb.facts) {
        // sub_list temp;
        temp = sub_list();
        temp = unify(lit, query, temp);
        if(!holds_alternative<string>(temp)){
            get<sub_list_type>(sub).insert(get<sub_list_type>(temp).begin(), get<sub_list_type>(temp).end());
            get<sub_list_type>(temp).clear();
        }
        // delete temp; // This isn't working
    }
    return sub;
}