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
    ast::Sentence CNF_s;
    CNF_s = ast::to_CNF(sentence);
    kb.sentences.push_back(CNF_s); // store original CNF converted sentence
    // does this lambda over the clauses in the sentence?
    visit(overloaded{
              [&](Literal<Term> literal) {
                  kb.facts.push_back(literal);
              },
              [&](Clause clause) {
                    kb.clauses.push_back(clause); // no definites for resolution inference
                  //for (auto literal : clause.literals) {
                      //kb.clauses.push_back(Clause{{literal}});
                  //}
              },
          },
          CNF_s);
}

// This will be the ask function for non-variable resolution
bool ask(KnowledgeBase& kb, ast::Sentence query) {
    // first we need to not the input sentence
    ast::Sentence not_query;
    not_query = query; // here we would apply some method to not the input parsed sentence

    // convert the input query into CNF form
    ast::Sentence cnf_query;
    cnf_query = ast::to_CNF(not_query);
    ast::CNF query_clauses(cnf_query);

    // now to start the resolution inference algorithm, this is just checking clauses
    // only need one clause to return empty because then the whole sentence is false, if want to check each clause, ask for each clause
    for (Clause c_kb : kb.clauses) {
        for (Clause c_q : query_clauses) {
            if((c_kb==c_q).literals.size() == 0) { // if we ever get a resolvant that is in contradiction with our kb, the resolution is true
                return true;
            }
        }
    }

    // now we check against the facts of kb incase the clauses didn't resolve it
    Clause kb_facts;
    kb_facts.literals.insert(literals.end(), kb.facts.begin(), kb.facts.end());

    for (Clause c_kb : kb_facts) {
        for (Clause c_q : query_clauses) {
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
sub_list ask_vars(KnowledgeBase& kb, ast::Literal query) {
    
    sub_list sub;
    for(Literal lit : kb.facts) {
        sub_list* temp = new sub_list;
        temp = unify(lit, query, temp);
        if(!holds_alternative<string>(temp)){

            get<sub_list_type>(sub).insert(get<sub_list_type>(temp).begin(), get<sub_list_type>(temp).end());
            get<sub_list_type>(temp).clear();
        }
        delete temp;
    }
    return sub;

}