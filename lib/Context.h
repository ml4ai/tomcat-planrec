#pragma once

#include "z3++.h"

class Context {
  private:
    static Context* instancePtr;

    Context () {}

  public:
    z3::context context;
    Context (const Context& obj)
      = delete;

    static Context* getInstance() {
      if (instancePtr == NULL) {
        instancePtr = new Context();
        return instancePtr;
      }
      else {
        return instancePtr;
      }
    }
};

Context *Context::instancePtr = NULL;
