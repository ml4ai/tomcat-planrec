#include "ast.hpp"
#include "../TermEquality.h"
#include "../ConnectedSentence.h"
#include "../QuantifiedSentence.h"

class FOLVisitor {
    auto visitPredicate(Predicate p, auto arg);

    auto visitTermEquality(TermEquality equality, auto arg);

    auto visitVariable(Variable variable, auto arg);

    auto visitConstant(Constant constant, auto arg);

    auto visitFunction(Function function, auto arg);

    auto visitNotSentence(NotSentence sentence, auto arg);

    auto visitConnectedSentence(ConnectedSentence sentence, auto arg);

    auto visitQuantifiedSentence(QuantifiedSentence sentence,
    auto arg);
};