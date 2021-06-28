#include "../AtomicSentence.h"
#include "../Term.h"
#include <string>
#include <vector>

class Predicate : AtomicSentence {
  private:
    string predicateName;
    vector<Term> terms;
    string stringRep = "";

  public:
    Predicate(string predicateName, vector<Term> terms) {
		this->predicateName = predicateName;
		this->terms.addAll(terms);
	}
        string getPredicateName() {
		return this->predicateName;
	}
        vector<Term> getTerms() {
		return this->terms;
	}
};