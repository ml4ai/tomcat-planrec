#include <boost/variant/recursive_variant.hpp>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

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
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
    os << "( ";
    for (auto x : v) {
        os << x << ' ';
    }
    os << ')';
    return os;
}

struct Symbol {
    const std::string name;
    std::string str() const { return this->name; }

    // Equality operator
    bool operator==(Symbol const& rhs) const { return this->name == rhs.name; }

    // Support for printing symbols
    friend std::ostream& operator<<(std::ostream& out, const Symbol& symbol) {
        out << symbol.str();
        return out;
    };
};

struct Constant : Symbol {};
struct Variable : Symbol {};
struct Function;

using Term = std::variant<Constant, Variable, Function>;

struct Function {
    std::string name;
    std::vector<Term> args = {};
};

struct Predicate {
    std::string name;
    std::vector<Term> args = {};
};

using Atom = std::variant<Constant, Variable, Predicate>;

using Expr = make_recursive_variant<Atom, std::vector<recursive_variant_>>::type;

struct Clause {
    std::vector<Predicate> literals;
};

struct KnowledgeBase {
    std::vector<Clause> clauses;
};


using Sentence = std::variant<Predicate, Clause>;

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
