#pragma once

//#include "parsing/FOLNode.h"
//#include "parsing/FOLVisitor.h"
#include "FOL.h"
#include <string>
#include <variant>
#include <vector>

// using Sentence = std::variant<Literal, Clause>;

std::string removeSpaces(std::string str) {
    str.erase(remove(str.begin(), str.end(), ' '), str.end());
    return str;
}

class Term : FOLNode {
    std::vector<Term> getArgs();
    Term copy();
};

class Variable : Term {
  private:
    std::string value;
    int indexical = -1;

  public:
    Variable(std::string s) { this->value = removeSpaces(s); }

    Variable(std::string s, int idx) {
        this->value = removeSpaces(s);
        this->indexical = idx;
    }

    std::string getValue() { return this->value; }
};

class Sentence : FOLNode {
    Sentence copy();
};

class AtomicSentence : Sentence {
    std::vector<Term> getArgs();

    AtomicSentence copy();
};

class Literal {
  private:
    AtomicSentence atom;
    bool negativeLiteral = false;
    std::string strRep = "";

  public:
    Literal(AtomicSentence atom) { this->atom = atom; }

    Literal(AtomicSentence atom, bool negated) {
        this->atom = atom;
        this->negativeLiteral = negated;
    }
};

class Clause {
    std::vector<Literal> literals;
};

class ConnectedSentence : Sentence {
  private:
    Sentence first, second;
    std::string connector;
    std::vector<Sentence> args;
    std::string stringRep = "";

  public:
    ConnectedSentence(std::string connector, Sentence first, Sentence second) {
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

    std::string getConnector() { return connector; }
};

class Connectors {
  public:
    inline const static std::string AND = "AND";

    inline const static std::string OR = "OR";

    inline const static std::string NOT = "NOT";

    inline const static std::string IMPLIES = "=>";

    inline const static std::string BICOND = "<=>";

    static bool isAND(std::string connector) { return !AND.compare(connector); }

    static bool isOR(std::string connector) { return !OR.compare(connector); }

    static bool isNOT(std::string connector) { return !NOT.compare(connector); }

    static bool isIMPLIES(std::string connector) {
        return !IMPLIES.compare(connector);
    }

    static int isBICOND(std::string connector) {
        return !BICOND.compare(connector);
    }
};

class Predicate : AtomicSentence {
  private:
    std::string predicateName;
    std::vector<Term> terms;
    std::string stringRep = "";

  public:
    Predicate(std::string predicateName, std::vector<Term> terms) {
        this->predicateName = predicateName;
        this->terms.insert(this->terms.end(), terms.begin(), terms.end());
        ;
    }
    std::string getPredicateName() { return this->predicateName; }
    std::vector<Term> getTerms() { return this->terms; }
};

class Constant : Term {
  private:
    std::string value;

  public:
    Constant(std::string s) { this->value = s; }

    std::string getValue() { return this->value; }

    accept(FOLVisitor v, auto arg) {
        return v.visitConstant(this, arg);
    }
};

class Function : Term {
  private:
    std::string functionName;
    std::vector<Term> terms;
    std::string stringRep = "";

  public:
    Function(std::string functionName, std::vector<Term> terms) {
        this->functionName = functionName;
        this->terms.insert(this->terms.end(), terms.begin(), terms.end());
    }

    std::string getFunctionName() { return this->functionName; }
    std::vector<Term> getTerms() { return this->terms; }
};

class NotSentence : Sentence {
  private:
    Sentence negated;
    std::vector<Sentence> args;
    std::string stringRep = "";

  public:
    NotSentence(Sentence negated) {
        this->negated = negated;
        this->args.push_back(negated);
    }

    Sentence getNegated() { return negated; };

    auto accept(FOLVisitor v, auto arg) {
        return v.visitNotSentence(this, arg);
    }
};

class QuantifiedSentence : Sentence {
  private:
    std::string quantifier;
    std::vector<Variable> variables;
    Sentence quantified;
    std::vector<FOLNode> args;
    std::string stringRep = "";

  public:
    QuantifiedSentence(std::string quantifier,
                       std::vector<Variable> variables,
                       Sentence quantified) {
        this->quantifier = quantifier;
        this->variables.insert(
            this->variables.end(), variables.begin(), variables.end());
        this->quantified = quantified;
        this->args.insert(this->args.end(), variables.begin(), variables.end());
        this->args.push_back(quantified);
    }

    std::string getQuantifier() { return this->quantifier; }
    std::vector<Variable> getVariables() { return this->variables; }

    auto accept(FOLVisitor v, auto arg) {
        return v.visitQuantifiedSentence(this, arg);
    }
};

class TermEquality : AtomicSentence {
  private:
    Term term1, term2;
    std::vector<Term> terms;
    std::string stringRep = "";

  public:
    static std::string getEqualitySynbol() { return "="; }
    TermEquality(Term term1, Term term2) {
        this->term1 = term1;
        this->term2 = term2;
        this->terms.push_back(term1);
        this->terms.push_back(term2);
    }

    Term getTerm1() { return this->term1; }

    Term getTerm2() { return this->term2; }
};
