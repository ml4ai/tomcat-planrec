#include "kb.h"

int main(int argc, char* argv[]) {
    auto c = Constant{"const"};
    auto v = Variable{"var"};
    auto v2 = Variable{"var"};
    // auto f = Function{"func"};
    auto p = Predicate{"pred"};
    auto kb = KnowledgeBase();
    tell(kb, p);

    return EXIT_SUCCESS;
}
