#include "Sentence.h"
#include "parsing/FOLVisitor.h"
#include <string>

class ConnectedSentence : Sentence {
  private:
    Sentence first, second;
    string connector;

  public:
    Sentence getFirst() { return first; }

    Sentence getSecond() { return second; }

    auto accept(FOLVisitor v, auto arg) {
        return v.visitConnectedSentence(this, arg);
    }

    string getConnector() {
        return connector;
    }
};