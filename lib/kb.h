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
#include "unification.h"


using namespace std;
using namespace fol;

// base data structs of the knowledge base to be populated using tell()
struct KnowledgeBase {
    vector<ast::Sentence> sentences; // this should be changed to the data type of CNF sentences 
    vector<Clause> clauses;
    vector<Clause> definite_clauses;
    vector<Literal<Term>> facts;
};

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
    // CNF converter to run on the sentence first
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
    for (int j=0; j < cnf.conjunctionOfClauses.size(); j++) {
        for (int i=0; i < cnf.conjunctionOfClauses.at(j).literals.size(); i++) {
            if (cnf.conjunctionOfClauses.at(j).literals.at(i).is_negative == false) {
                cnf.conjunctionOfClauses.at(j).literals.at(i).is_negative = true;
            }
            else {
                cnf.conjunctionOfClauses.at(j).literals.at(i).is_negative = false;
            }
        }
    }
    // after having swapped all the negations, we now interpret cnf as dnf, and clause as a conjuction of literals not disjunction

    // the application of the distribution rule over the disjunctions and conjuctions now results in taking one literal from each "conjuctive-clause"
    // in the dnf sentence and making a clause out of it, and then permuting through all options conjucting each clause, which is a cnf sentence at the end
    ast::Sentence for_cnf;
    ast::CNF temp1 = ast::construct(for_cnf);
    temp1.conjunctionOfClauses.clear();
    ast::CNF temp2 = ast::construct(for_cnf); // these are adding empty clauses, need to clear them 
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
    
    // we compile a large list of all clauses in KB, including one clause of 
    typedef vector<Clause> clause_vector;
    clause_vector clause_vec;
    clause_vector temp_vec;
    clause_vector fact_vec;
    Clause kb_facts, temp, resolvant;
    // Each fact is a seperate clause
    for(Literal<Term> l1 : kb.facts) {
        kb_facts.literals.push_back(l1);
        fact_vec.push_back(kb_facts);
        kb_facts.literals.clear();
    }
    clause_vec.insert(clause_vec.end(), fact_vec.begin(), fact_vec.end());
    // adding the clauses of the query
    for (Clause c_q : query_clauses.conjunctionOfClauses) {
        clause_vec.push_back(c_q);
    }
    // adding the rule clauses of the KB
    for (Clause c_kb : kb.clauses) {
        clause_vec.push_back(c_kb);
    }

    bool cond=false;
    bool found=false;
    // now to run the resolution 
    while (cond == false) {
        for (int i=0; i < clause_vec.size(); i++) {
            for (int j=0; j < clause_vec.size(); j++) {
                if (i!=j) {
                    resolvant = clause_vec.at(i)==clause_vec.at(j);
                    if (resolvant.literals.size() == 0) {
                        return true;
                        cond = true;
                    }
                    else { 
                        for (Clause c_o : clause_vec) {
                            bool vec_eq=false;
                            int found_count=0;
                            if (resolvant.literals.size() == c_o.literals.size()) {
                                for (int l=0; l < resolvant.literals.size(); l++) {
                                    for (int ll=0; ll < resolvant.literals.size(); ll++){
                                        if (resolvant.literals.at(l)==c_o.literals.at(ll)) {
                                            found_count = found_count + 1;
                                            break;
                                        }
                                    }
                                }
                                if (found_count == resolvant.literals.size()) {
                                    vec_eq=true;
                                }
                            }
                            if (vec_eq==true) {
                                found = true; // check if resolvant is a new clause
                            }
                        }
                        if (found == false) { // if new, add it to list
                            temp_vec.push_back(resolvant);
                        }
                        found = false; // reset found condition
                    }
                }
            }
        }
        // resolution fail condition is no new resolutions are produced, thus KB is self consistant 
        if (temp_vec.size() == 0) { // This should be the case that all resolvants have been added and no new ones are created
            return false;
            cond = true;
        }
        clause_vec.insert(clause_vec.end(), temp_vec.begin(), temp_vec.end());
        temp_vec.clear();
    }
}
 // overloaded option for CNF input instead of parsed sentence
bool ask(KnowledgeBase& kb, ast::CNF query) {
    // convert the input query into CNF form
    ast::CNF query_clauses = not_CNF(query);
    // now to start the resolution inference algorithm, this is just checking clauses
    // only need one clause to return empty because then the whole sentence is false, if want to check each clause, ask for each clause

    // we compile a large list of all clauses in KB, including one clause of 
    typedef vector<Clause> clause_vector;
    clause_vector clause_vec;
    clause_vector temp_vec;
    clause_vector fact_vec;
    Clause kb_facts, temp, resolvant;
    // Each fact is a seperate clause
    for(Literal<Term> l1 : kb.facts) {
        kb_facts.literals.push_back(l1);
        fact_vec.push_back(kb_facts);
        kb_facts.literals.clear();
    }
    clause_vec.insert(clause_vec.end(), fact_vec.begin(), fact_vec.end());
    // adding the clauses of the query
    for (Clause c_q : query_clauses.conjunctionOfClauses) {
        clause_vec.push_back(c_q);
    }
    // adding the rule clauses of the KB
    for (Clause c_kb : kb.clauses) {
        clause_vec.push_back(c_kb);
    }

    bool cond=false;
    bool found=false;
    // now to run the resolution 
    while (cond == false) {
        for (int i=0; i < clause_vec.size(); i++) {
            for (int j=0; j < clause_vec.size(); j++) {
                if (i!=j) {
                    resolvant = clause_vec.at(i)==clause_vec.at(j);
                    if (resolvant.literals.size() == 0) {
                        return true;
                        cond = true;
                    }
                    else { 
                        for (Clause c_o : clause_vec) {
                            bool vec_eq=false;
                            int found_count=0;
                            if (resolvant.literals.size() == c_o.literals.size()) {
                                for (int l=0; l < resolvant.literals.size(); l++) {
                                    for (int ll=0; ll < resolvant.literals.size(); ll++){
                                        if (resolvant.literals.at(l)==c_o.literals.at(ll)) {
                                            found_count = found_count + 1;
                                            break;
                                        }
                                    }
                                }
                                if (found_count == resolvant.literals.size()) {
                                    vec_eq=true;
                                }
                            }
                            if (vec_eq==true) {
                                found = true; // check if resolvant is a new clause
                            }
                        }
                        if (found == false) { // if new, add it to list
                            temp_vec.push_back(resolvant);
                        }
                        found = false; // reset found condition
                    }
                }
            }
        }
        // resolution fail condition is no new resolutions are produced, thus KB is self consistant 
        if (temp_vec.size() == 0) { // This should be the case that all resolvants have been added and no new ones are created
            return false;
            cond = true;
        }
        clause_vec.insert(clause_vec.end(), temp_vec.begin(), temp_vec.end());
        temp_vec.clear();
    }
}

// now for the ask_vars method, which will return a substitution list for a variable in the query, if resolute 
// we do not have the standard aparting implemented right now, we are operating on each variable input will have a 
// unqiue name

// unless we restrict ourselves to horn clauses the inputs to the ask_vars will have to be a literal and it will just be unified against the facts
// of the kb. AIMA p.301 for detials.

// UNDER CONSTRUCTION

// This will return a vector of substitutions all of which are allowed for the given input
/* ask_vars(KnowledgeBase& kb, Literal<Term> query) {
    // sub_optional sub;
    for(Literal lit : kb.facts) {
        auto sub = unify(lit, query);
    }
    return sub;
} */