#include "Sentence.h"
#include <string>
#include "parsing/FOLVisitor.h"

class QuantifiedSentence: Sentence{

    QuantifiedSentence(String quantifier, List<Variable> variables,
                       Sentence quantified) {
        this.quantifier = quantifier;
        this.variables.addAll(variables);
        this.quantified = quantified;
        this.args.addAll(variables);
        this.args.add(quantified);
    }

    auto accept(FOLVisitor v, auto arg) {
        return v.visitQuantifiedSentence(this, arg);
    }
};