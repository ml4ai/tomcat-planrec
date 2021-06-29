#pragma once

#include "Symbol.h"

struct Variable : Symbol {
        friend bool operator==(const Variable &lhs, const Variable &rhs) {
                bool eq=false;
                if (lhs.name == rhs.name) {
                    eq=true; // any variable means they aren't unified
                }
                return eq; // add condition where each element are equal
            }
};
