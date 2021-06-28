#include "AtomicSentence.h"
#include "Term.h"
#include <string>
#include <vector>

class TermEquality : AtomicSentence {
  private:
    Term term1, term2;
    std::vector<Term> terms;
    string stringRep = "";

  public:
    static string getEqualitySynbol() { return "="; }
    TermEquality(Term term1, Term term2) {
        this->term1 = term1;
        this->term2 = term2;
        this->terms.push_back(term1);
        this->terms.push_back(term2);
    }

    Term getTerm1() { return this->term1; }

    Term getTerm2() { return this->term2; }
};