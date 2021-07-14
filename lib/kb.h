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
// this methos returns whether clause is definite or not, only exactly one positive literal.
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
                  if (isDefiniteClause(clause)) {
                      kb.definite_clauses.push_back(clause);
                  }
                  else {
                      kb.clauses.push_back(clause);
                  }
                  //for (auto literal : clause.literals) {
                      //kb.clauses.push_back(Clause{{literal}});
                  //}
              },
          },
          CNF_s);
}
