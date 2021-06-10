#include <boost/variant/recursive_variant.hpp>
#include <iostream>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

using namespace std;
using boost::recursive_variant_, boost::make_recursive_variant;

struct Constant {
    string name;
    friend ostream& operator<<(ostream& out, const Constant& constant) {
        out << constant.name;
        return out;
    };
};

struct Variable {
    string name;
    friend ostream& operator<<(ostream& out, const Variable& variable) {
        out << variable.name;
        return out;
    };
};

struct Function;

using Term = variant<Constant, Variable, Function>;

struct Function {
    string name;
    vector<Term> args;
    friend ostream& operator<<(ostream& out, const Function& f) {
        out << "( " << f.name << ' ';
        for (auto arg : f.args) {
            visit([&](auto&& x) { out << x << ' '; }, arg);
        };
        out << ')';
        return out;
    };
};


struct Predicate {
    string name;
    vector<Term> args;
    friend ostream& operator<<(ostream& out, const Predicate& predicate) {
        out << "( " << predicate.name << ' ';
        for (auto arg : predicate.args) {
            visit([&](auto&& x) { out << x << ' '; }, arg);
        };
        out << ')';
        return out;
    };
};

enum LogicalConnective { Not, And, Or, Implies, Iff };

enum Quantifier { Forall, Exists };

struct ComplexSentence;

using AtomicSentence = Predicate;

using Sentence = make_recursive_variant<
    AtomicSentence,
    tuple<LogicalConnective, recursive_variant_>, // Negated sentences
    tuple<LogicalConnective,
          recursive_variant_,
          recursive_variant_>, // and/or/implies/iff
    tuple<Quantifier, vector<Variable>, recursive_variant_> // quantified
                                                            // sentence
    >::type;

using NotSentence = tuple<LogicalConnective, Sentence>;
using ConnectedSentence = tuple<LogicalConnective, Sentence, Sentence>;
using QuantifiedSentence = tuple<Quantifier, vector<Variable>, Sentence>;

struct KnowledgeBase {
    vector<Sentence> sentences;
};

int main(int argc, char* argv[]) {
    auto c = Constant{"c"};
    auto v = Variable{"v"};
    auto p = Predicate{"p", {c, v}};
    auto f = Function{"func", {c, v}};
    cout << p << endl;
    cout << f << endl;

    return EXIT_SUCCESS;
}
