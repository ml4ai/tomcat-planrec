#pragma once

#include "Symbol.h"
#include "Term.h"
#include <string>

// struct Variable : Symbol {};

class Variable : Term {
  private:
    string value;
    int indexical = -1;

  public:
    Variable(string s) {
        this->value = s.erase(
            std::remove_if(s.begin(),
                           s.end(),
                           [](unsigned char x) { return std::isspace(x); }),
            string.end());
    }

    Variable(string s, int idx) {
        this->value = s.erase(
            std::remove_if(s.begin(),
                           s.end(),
                           [](unsigned char x) { return std::isspace(x); }),
            string.end());
        this->indexical = idx;
    }

    string getValue() { return this->value; }
};
