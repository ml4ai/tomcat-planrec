#include <boost/variant/recursive_variant.hpp>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

using namespace std;
using boost::recursive_variant_, boost::make_recursive_variant;

// Helpers for std::visit
template <class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


// Support for printing variants
template <typename T, typename... Ts>
std::ostream& operator<<(std::ostream& os, const std::variant<T, Ts...>& v) {
    std::visit([&os](auto&& arg) { os << arg; }, v);
    return os;
}

// Define support for printing vectors
template <typename T>
std::ostream& operator<<(std::ostream& os, const vector<T>& v) {
    os << "( ";
    for (auto x : v) {
        os << x << ' ';
    }
    os << ')';
    return os;
}

struct Symbol {
    const string name;
    string str() const { return this->name; }

    // Equality operator
    bool operator==(Symbol const& rhs) const { return this->name == rhs.name; }

    // Support for printing symbols
    friend ostream& operator<<(ostream& out, const Symbol& symbol) {
        out << symbol.str();
        return out;
    };
};

struct Constant : Symbol {};
struct Variable : Symbol {};
struct Function;

using Term = variant<Constant, Variable, Function>;

struct Function {
    string name;
    vector<Term> args = {};
};

struct Predicate {
    string name;
    vector<Term> args = {};
};

using Atom = variant<Constant, Variable, Predicate, Function>;

using Expr = make_recursive_variant<Atom, vector<recursive_variant_>>::type;

struct Clause {
    vector<Predicate> literals;
};

struct KnowledgeBase {
    vector<Clause> clauses;
};


using Sentence = variant<Predicate, Clause>;

void tell(KnowledgeBase& kb, Sentence sentence) {
    visit(overloaded{
              [&](Predicate predicate) { kb.clauses.push_back(Clause{{predicate}}); },
              [&](Clause clause) {
                  for (auto predicate : clause.literals) {
                      kb.clauses.push_back(Clause{{predicate}});
                  }
              },
          },
          sentence);
}

int main(int argc, char* argv[]) {
    auto c = Constant{"const"};
    auto v = Variable{"var"};
    auto v2 = Variable{"var"};
    // auto f = Function{"func"};
    auto p = Predicate{"pred", {c, v}};
    auto clause = Clause();
    clause.literals.push_back(p);
    auto kb = KnowledgeBase();
    tell(kb, p);
    tell(kb, clause);

    return EXIT_SUCCESS;
}
