#include "ParseTreeNode.h"
#include <string>
#include <vector>

class FOLNode: ParseTreeNode {
    string getSymbolicName();

    bool isCompound();

    vector<FOLNode> getArgs();

    auto accept(FOLVisitor v, auto arg);

    FOLNode copy();
};