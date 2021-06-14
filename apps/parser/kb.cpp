#include <boost/variant/recursive_variant.hpp>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

using namespace std;
using boost::recursive_variant_, boost::make_recursive_variant;

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

using Atom = variant<Constant, Variable, Predicate>;

using Expr = make_recursive_variant<Atom, vector<recursive_variant_>>::type;

struct KnowledgeBase {
    vector<Predicate> literals;
};

struct Clause {
    vector<Predicate> literals;
};

template <class... Ts> struct overloaded : Ts... { using Ts::operator()...; };

template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

using Sentence = variant<Predicate, Clause>;

void tell(KnowledgeBase& kb, Sentence sentence) {
    visit(overloaded{
              [&](Predicate predicate) { kb.literals.push_back(predicate); },
              [&](Clause clause) {
                  for (auto predicate : clause.literals) {
                      kb.literals.push_back(predicate);
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
    auto p = Predicate{"pred"};
    auto kb = KnowledgeBase();
    tell(kb, p);

    return EXIT_SUCCESS;
}
