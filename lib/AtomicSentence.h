#include "Sentence.h"
#include "Term.h"
#include <vector>

class AtomicSentence: Sentence {
	vector<Term> getArgs();

	AtomicSentence copy();
};