#pragma once

#include "../fol/Constant.h"
#include "../fol/Function.h"
#include "../fol/Literal.h"
#include "../fol/Predicate.h"
#include "../fol/Term.h"
#include "../fol/Variable.h"
#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include <boost/variant/recursive_wrapper.hpp>
#include <iostream>
#include <string>
#include <tuple>
#include <unordered_set>

// TODO Enforce optionality wherever appropriate, based on EBNF specification.

namespace ast {
    using Name = std::string;
    namespace x3 = boost::spirit::x3;

    // Import some classes that are more generally useful
    using fol::Constant;
    using fol::Literal;
    using fol::Predicate;
    using fol::Term;
    using fol::Variable;

    using PrimitiveType = std::string;

    using EitherType = std::unordered_set<PrimitiveType>;

    // Whenever we don't have recursive variants, we use x3::variant instead of
    // boost::variant, so we get a distinct type.
    struct Type : x3::variant<PrimitiveType, EitherType> {
        using base_type::base_type;
        using base_type::operator=;
    };

    template <class T> using ImplicitlyTypedList = std::vector<T>;

    template <class T> struct ExplicitlyTypedList {
        std::vector<T> entries;
        Type type;
    };

    template <class T> struct TypedList {
        std::vector<ExplicitlyTypedList<T>> explicitly_typed_lists;
        std::optional<ImplicitlyTypedList<T>> implicitly_typed_list;
    };

    struct AtomicFormulaSkeleton : x3::position_tagged {
        Predicate predicate;
        TypedList<Variable> variables;
    };

    struct Nil : x3::position_tagged {
        bool operator==(const Nil& nil) const;
    };

    template <class T> struct AtomicFormula {
        Predicate predicate;
        std::vector<T> args;
    };

    // Forward declare classes in order to work with Boost's recursive_wrapper
    struct ConnectedSentence;
    struct NotSentence;
    struct ImplySentence;
    struct QuantifiedSentence;

    struct EqualsSentence : x3::position_tagged {
        Term lhs;
        Term rhs;
    };

    struct NotEqualsSentence : x3::position_tagged {
        Term lhs;
        Term rhs;
    };

    using Sentence =
        boost::variant<Nil,
                       Literal<Term>,
                       boost::recursive_wrapper<ConnectedSentence>,
                       boost::recursive_wrapper<NotSentence>,
                       boost::recursive_wrapper<ImplySentence>,
                       boost::recursive_wrapper<QuantifiedSentence>,
                       EqualsSentence>;

    struct ConnectedSentence : x3::position_tagged {
        std::string connector;
        std::vector<Sentence> sentences;
    };

    struct NotSentence : x3::position_tagged {
        Sentence sentence;
    };

    struct ImplySentence : x3::position_tagged {
        Sentence sentence1;
        Sentence sentence2;
    };

    struct QuantifiedSentence : x3::position_tagged {
        std::string quantifier;
        TypedList<Variable> variables;
        Sentence sentence;
    };

    struct Constraint : x3::variant<Nil, EqualsSentence, NotEqualsSentence> {
        using base_type::base_type;
        using base_type::operator=;
    };

    struct Constraints : x3::variant<Nil, Constraint, std::vector<Constraint>> {
        using base_type::base_type;
        using base_type::operator=;
    };

    // Abstract Tasks
    struct Task : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
    };

    // Task that a method decomposes
    struct MTask : x3::position_tagged {
        Name name;
        std::vector<Term> parameters;
    };

    struct SubTaskWithId : x3::position_tagged {
        Name id;
        MTask subtask;
    };

    struct SubTask : x3::variant<MTask, SubTaskWithId> {
        using base_type::base_type;
        using base_type::operator=;
    };

    struct SubTasks : x3::variant<Nil, SubTask, std::vector<SubTask>> {
        using base_type::base_type;
        using base_type::operator=;
    };

    struct Ordering : x3::position_tagged {
        Name first;
        Name second;
    };

    struct Orderings : x3::variant<Nil, Ordering, std::vector<Ordering>> {
        using base_type::base_type;
        using base_type::operator=;
    };

    struct MethodSubTasks : x3::position_tagged {
        std::string ordering_kw;
        SubTasks subtasks;
    };

    struct TaskNetwork : x3::position_tagged {
        std::optional<MethodSubTasks> subtasks;
        std::optional<Orderings> orderings;
        std::optional<Constraints> constraints;
    };

    // Totally-ordered methods use the keyword 'ordered-subtasks'
    // Partially-ordered methods use the keyword 'subtasks'
    struct Method : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
        MTask task;
        Sentence precondition; // optional
        TaskNetwork task_network;
    };

    // Conditional effects
    using PEffect = Literal<Term>;
    using CondEffect = boost::variant<PEffect, std::vector<PEffect>>;

    struct WhenCEffect;
    struct ForallCEffect;
    struct AndCEffect;

    using CEffect = boost::variant<boost::recursive_wrapper<ForallCEffect>,
                                   boost::recursive_wrapper<WhenCEffect>,
                                   PEffect>;

    using Effect =
        boost::variant<Nil, boost::recursive_wrapper<AndCEffect>, CEffect>;

    struct WhenCEffect {
        Sentence gd;
        CondEffect cond_effect;
    };

    struct ForallCEffect {
        std::vector<Variable> variables;
        Effect effect;
    };

    struct AndCEffect {
        std::vector<CEffect> c_effects;
    };

    // Primitive Actions
    struct Action : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
        Sentence precondition;
        Effect effect;
    };

    struct Domain : x3::position_tagged {
        Name name;
        std::vector<std::string> requirements;
        TypedList<Name> types;
        TypedList<Name> constants;
        std::vector<AtomicFormulaSkeleton> predicates;
        std::vector<Task> tasks;
        std::vector<Method> methods;
        std::vector<Action> actions;
    };

    struct ProblemHTN : x3::position_tagged {
        std::string problem_class;
        TypedList<Variable> parameters;
        TaskNetwork task_network;
    };

    using Init = std::vector<Literal<Name>>;

    struct Problem : x3::position_tagged {
        Name name;
        Name domain_name;
        std::vector<std::string> requirements;
        TypedList<Name> objects;
        ProblemHTN problem_htn;
        Init init;
        Sentence goal;
    };

    using boost::fusion::operator<<;
} // namespace ast
