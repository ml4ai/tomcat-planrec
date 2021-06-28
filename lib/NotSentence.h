#include "Sentence.h"
#include <vector>
#include <string>
#include "parsing/FOLVisitor.h"

class NotSentence: Sentence{
  private:
    Sentence negated;
    vector<Sentence> args;
    string stringRep = "";

  public:
    NotSentence(Sentence negated) {
        this->negated = negated;
        this->args.push_back(negated);
    }

    Sentence getNegated() {
        return negated;
    };

    auto accept(FOLVisitor v, auto arg) {
        return v.visitNotSentence(this, arg);
    }


};