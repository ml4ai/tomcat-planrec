#include "../Term.h"
#include "FOLVisitor.h"
#include <string>

class Constant: Term{
  private:
    string value;

  public:
    Constant(string s) {
        this->value = s;
	}
        string getValue() {
            return this->value;
	}
        accept(FOLVisitor v, auto arg) {
		return v.visitConstant(this, arg);
	}
};