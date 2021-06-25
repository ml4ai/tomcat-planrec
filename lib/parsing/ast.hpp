#pragma once

#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/variant/recursive_wrapper.hpp>
#include <iostream>
#include <string>
#include <tuple>
#include <unordered_set>
#include "../fol/Variable.h"
#include "../fol/Constant.h"
#include "../fol/Predicate.h"
#include "../fol/Term.h"
#include "../fol/Function.h"

namespace ast {
    using Name = std::string;
    namespace x3 = boost::spirit::x3;

    // Import some classes that are more generally useful
    using fol::Variable;
    using fol::Constant;
    using fol::Term;
    using fol::Predicate;

    struct PrimitiveType {
        Name name;
        bool operator==(const PrimitiveType& primitive_type) const;
        struct hash {
            std::size_t operator()(PrimitiveType const& type) const noexcept {
                return std::hash<std::string>{}(type.name);
            }
        };
    };

    struct EitherType {
        std::unordered_set<PrimitiveType, PrimitiveType::hash> primitive_types;
    };

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

    template<class T>
    struct Literal {
        AtomicFormula<T> atomic_formula;
        bool is_negative = false;
    };


    // Forward declare classes in order to work with Boost's recursive_wrapper
    struct AndSentence;
    struct OrSentence;
    struct NotSentence;
    struct ImplySentence;

    using Sentence = boost::variant<Nil,
                                    AtomicFormula<Term>,
                                    Literal<Term>,
                                    boost::recursive_wrapper<AndSentence>,
                                    boost::recursive_wrapper<OrSentence>,
                                    boost::recursive_wrapper<NotSentence>,
                                    boost::recursive_wrapper<ImplySentence>>;

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
