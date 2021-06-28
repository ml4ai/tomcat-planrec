#include "Sentence.h"
#include "parsing/FOLVisitor.h"
#include <string>
#include <vector>

class ConnectedSentence : Sentence {
  private:
    Sentence first, second;
    string connector;
    vector<Sentence> args;
    string stringRep = "";

  public:
    ConnectedSentence(string connector, Sentence first, Sentence second) {
		this->connector = connector;
		this->first = first;
		this->second = second;
		this->args.push_back(first);
		this->args.push_back(second);
	}

    Sentence getFirst() { return first; }

    Sentence getSecond() { return second; }

    auto accept(FOLVisitor v, auto arg) {
        return v.visitConnectedSentence(this, arg);
    }

    string getConnector() {
        return connector;
    }
};