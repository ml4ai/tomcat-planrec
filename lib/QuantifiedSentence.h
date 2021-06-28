#include "Sentence.h"
#include "Variable.h"
#include "parsing/FOLNode.h"
#include "parsing/FOLVisitor.h"
#include <string>
#include <vector>

class QuantifiedSentence : Sentence {
  private:
    string quantifier;
    vector<Variable> variables;
    Sentence quantified;
    vector<FOLNode> args;
    string stringRep = "";

  public:
    QuantifiedSentence(string quantifier,
                       vector<Variable> variables,
                       Sentence quantified) {
        this->quantifier = quantifier;
        this->variables.addAll(variables);
        this->quantified = quantified;
        this->args.addAll(variables);
        this->args.add(quantified);
    }

    string getQuantifier() { return this->quantifier; }
    vector<Variable> getVariables() { return this->variables; }

    auto accept(FOLVisitor v, auto arg) {
        return v.visitQuantifiedSentence(this, arg);
    }
};