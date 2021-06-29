#pragma once

#include "Clause.h"
#include "Literal.h"
#include "Sentence.h"
#include "util.h"
#include <iostream>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

struct KnowledgeBase {
    std::vector<Clause> clauses;
};

void tell(KnowledgeBase& kb, Sentence sentence) {
    visit(overloaded{
              [&](Literal literal) {
                  kb.clauses.push_back(Clause{{literal}});
              },
              [&](Clause clause) {
                  for (auto literal : clause.literals) {
                      kb.clauses.push_back(Clause{{literal}});
                  }
              },
          },
          sentence);
}
