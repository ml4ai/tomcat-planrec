#pragma once

#include "../fol/Constant.h"
#include "../fol/Function.h"
#include "../fol/Predicate.h"
#include "../fol/Term.h"
#include "../fol/Variable.h"
#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/variant/recursive_wrapper.hpp>
#include <iostream>
#include <string>
#include <tuple>
#include <unordered_set>

namespace ast {
    using Name = std::string;
    namespace x3 = boost::spirit::x3;

    // Import some classes that are more generally useful
    using fol::Constant;
    using fol::Predicate;
    using fol::Term;
    using fol::Variable;

    using PrimitiveType = std::string;

    using EitherType = std::unordered_set<PrimitiveType>;

    using Type = boost::variant<PrimitiveType, EitherType>;

    template <class T> using ImplicitlyTypedList = std::vector<T>;

    template <class T> struct ExplicitlyTypedList {
        std::vector<T> entries;
        Type type;
    };

    template <class T> struct TypedList {
        std::vector<ExplicitlyTypedList<T>> explicitly_typed_lists;
        boost::optional<ImplicitlyTypedList<T>> implicitly_typed_list;
    };

    struct AtomicFormulaSkeleton : x3::position_tagged {
        Predicate predicate;
        TypedList<Variable> variables;
    };

    struct Nil {
        bool operator==(const Nil& nil) const;
    };

    template <class T> struct AtomicFormula {
        Predicate predicate;
        std::vector<T> args;
    };

    template <class T> struct NegativeLiteral {
        AtomicFormula<T> atomic_formula;
    };

    template <class T>
    using Literal = boost::variant<AtomicFormula<T>, NegativeLiteral<T>>;

    // Forward declare classes in order to work with Boost's recursive_wrapper
    struct AndSentence;
    struct OrSentence;
    struct NotSentence;
    struct ImplySentence;
    struct ExistsSentence;
    struct ForallSentence;

    using Sentence = boost::variant<Nil,
                                    AtomicFormula<Term>,
                                    Literal<Term>,
                                    boost::recursive_wrapper<AndSentence>,
                                    boost::recursive_wrapper<OrSentence>,
                                    boost::recursive_wrapper<NotSentence>,
                                    boost::recursive_wrapper<ImplySentence>,
                                    boost::recursive_wrapper<ExistsSentence>,
                                    boost::recursive_wrapper<ForallSentence>>;

    // TODO add quantified sentences

    struct AndSentence {
        std::vector<Sentence> sentences;
    };

    struct OrSentence {
        std::vector<Sentence> sentences;
    };

    struct NotSentence {
        Sentence sentence;
    };

    struct ImplySentence {
        Sentence sentence1;
        Sentence sentence2;
    };

    struct ExistsSentence {
        std::vector<TypedList<Variable>> variables;
        Sentence sentence;
    };

    struct ForallSentence {
        std::vector<TypedList<Variable>> variables;
        Sentence sentence;
    };

    struct Domain : x3::position_tagged {
        Name name;
        std::vector<std::string> requirements;
        TypedList<Name> types;
        TypedList<Name> constants;
        std::vector<AtomicFormulaSkeleton> predicates;
        // std::vector<Action> actions;
    };

    struct Problem : x3::position_tagged {
        Name name;                             // to just get name of problem
        Name domain_name;                      // for domain association
        std::vector<std::string> requirements; // for any problem requirements
        TypedList<Name> objects;
    }; // end problem struct

    // struct Action : x3::position_tagged {
    // Name name;
    // std::vector<Variable> parameters;
    //};

    using boost::fusion::operator<<;
} // namespace ast
