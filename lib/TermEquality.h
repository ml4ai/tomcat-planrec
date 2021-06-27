//
// Created by Liang Zhang on 6/26/21.
//

#ifndef PROJECTNAME_TERMEQUALITY_H
#define PROJECTNAME_TERMEQUALITY_H

#endif // PROJECTNAME_TERMEQUALITY_H
#include "AtomicSentence.h"
#include "Term.h"
#include <vector>
#include <string>

class TermEquality: AtomicSentence {
    Term term1, term2;
    vector<Term> terms;
    string stringRep = NULL;
    int hashCode = 0;
};