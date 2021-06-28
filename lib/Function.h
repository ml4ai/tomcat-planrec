#pragma once

#include "Term.h"
#include <string>
#include <vector>

//struct Function {
//    std::string name;
//    std::vector<Term> args = {};
//};

class Function: Term{
  private:
    string functionName;
    vector<Term> terms;
    string stringRep = "";

  public:
    Function(string functionName, vector<Term> terms) {
		this->functionName = functionName;
		this->terms.push_back(terms);
	}

        string getFunctionName() {
		return this->functionName;
	}
        vector<Term> getTerms() {
		return this->terms;
	}
};