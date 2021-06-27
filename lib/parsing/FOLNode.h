//
// Created by Liang Zhang on 6/26/21.
//

#ifndef PROJECTNAME_FOLNODE_H
#define PROJECTNAME_FOLNODE_H

#endif // PROJECTNAME_FOLNODE_H

#include "ParseTreeNode.h"
#include <string>
#include <vector>

class FOLNode: ParseTreeNode {
    string getSymbolicName();

    bool isCompound();

    vector<FOLNode> getArgs();

    auto accept(FOLVisitor v, auto arg);

    FOLNode copy();
}