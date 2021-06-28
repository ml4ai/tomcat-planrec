#include "Sentence.h"
#include <string>
#include <vector>

class ParseTreeNode {};

class FOLVisitor {
    auto visitPredicate(Predicate p, auto arg);

    auto visitTermEquality(TermEquality equality, auto arg);

    auto visitVariable(Variable variable, auto arg);

    auto visitConstant(Constant constant, auto arg);

    auto visitFunction(Function function, auto arg);

    auto visitNotSentence(NotSentence sentence, auto arg);

    auto visitConnectedSentence(ConnectedSentence sentence, auto arg);

    auto visitQuantifiedSentence(QuantifiedSentence sentence, auto arg);
};

class FOLNode : ParseTreeNode {
  public:
    std::string getSymbolicName();

    bool isCompound();

    std::vector<FOLNode> getArgs();

    auto accept(FOLVisitor v, auto arg);

    FOLNode copy();
};

class AbstractFOLVisitor : FOLVisitor {
  public:
    AbstractFOLVisitor();

  protected:
    Sentence recreate(auto ast) { return ((Sentence)ast).copy(); }

  public:
    auto visitVariable(Variable variable, auto arg) { return variable.copy(); }

    auto visitQuantifiedSentence(QuantifiedSentence sentence, auto arg) {
        std::vector<Variable> variables;
        for (Variable var : sentence.getVariables()) {
            variables.push_back((Variable)var.accept(this, arg));
        }

        return new QuantifiedSentence(
            sentence.getQuantifier(),
            variables,
            (Sentence)sentence.getQuantified().accept(this, arg));
    }

    auto visitPredicate(Predicate predicate, auto arg) {
        vector<Term> terms = predicate.getTerms();
        vector<Term> newTerms;
        for (int i = 0; i < terms.size(); i++) {
            Term t = terms[i];
            Term subsTerm = (Term)t.accept(this, arg);
            newTerms.push_back(subsTerm);
        }
        return new Predicate(predicate.getPredicateName(), newTerms);
    }

    auto visitTermEquality(TermEquality equality, auto arg) {
        Term newTerm1 = (Term)equality.getTerm1().accept(this, arg);
        Term newTerm2 = (Term)equality.getTerm2().accept(this, arg);
        return new TermEquality(newTerm1, newTerm2);
    }

    auto visitConstant(Constant constant, auto arg) { return constant; }

    auto visitFunction(Function function, auto arg) {
        vector<Term> terms = function.getTerms();
        vector<Term> newTerms = new Arrayvector<Term>();
        for (int i = 0; i < terms.size(); i++) {
            Term t = terms.get(i);
            Term subsTerm = (Term)t.accept(this, arg);
            newTerms.add(subsTerm);
        }
        return new Function(function.getFunctionName(), newTerms);
    }

    auto visitNotSentence(NotSentence sentence, auto arg) {
        return new NotSentence(
            (Sentence)sentence.getNegated().accept(this, arg));
    }

    auto visitConnectedSentence(ConnectedSentence sentence, auto arg) {
        Sentence substFirst = (Sentence)sentence.getFirst().accept(this, arg);
        Sentence substSecond = (Sentence)sentence.getSecond().accept(this, arg);
        return new ConnectedSentence(
            sentence.getConnector(), substFirst, substSecond);
    }
};

class FOLParser {};

class SubstVisitor : AbstractFOLVisitor {
  public:
    SubstVisitor();
};