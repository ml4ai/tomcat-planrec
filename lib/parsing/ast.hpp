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
#include <optional>

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

    // TypedList EBNF Definition:
        // typed list (x)> ::= x+ - <type> [<typed list (x)>]
    template <class T> struct TypedList {
        std::vector<ExplicitlyTypedList<T>> explicitly_typed_lists;
        ImplicitlyTypedList<T> implicitly_typed_list = {};
    };

    // AtomicFormulaSkeleton EBNF Definition:
        // <atomic-formula-skeleton> ::= (<predicate> <typed list (variable)>)
        // <predicate> ::= <name>
    struct AtomicFormulaSkeleton : x3::position_tagged {
        Predicate predicate;
        TypedList<Variable> variables;
    };

    // Nil EBNF Definition: <gd> ::= ()
    struct Nil : x3::position_tagged {
        bool operator==(const Nil& nil) const;
    };

    // AtomicFormula EBNF Definition:
        // <atomic formula(t)> ::= (<predicate> t*)
    template <class T> struct AtomicFormula {
        Predicate predicate;
        std::vector<T> args;
    };

    // Forward declare classes in order to work with Boost's recursive_wrapper
    struct ConnectedSentence;
    struct NotSentence;
    struct ImplySentence;
    struct QuantifiedSentence;
    struct NotEqualsSentence;

    // EqualsSentence EBNF Definition:  <gd> ::= (= <term> <term>)
    struct EqualsSentence {
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
                       EqualsSentence,
                       boost::recursive_wrapper<NotEqualsSentence>>;

    // ConnectedSentence EBNF Definition: requires disjunctive-preconditions
        // <gd> ::= (and <gd>*)
        // <gd> ::= (or <gd>*)
    struct ConnectedSentence {
        std::string connector;
        std::vector<Sentence> sentences;
    };

    // NotSentence EBNF Definition: requires disjunctive-preconditions
        // <gd> ::= (not <gd>)
    struct NotSentence {
        Sentence sentence;
    };

    // ImplySentence EBNF Definition: requires disjunctive-preconditions
        // <gd> ::= (imply <gd> <gd>)
    struct ImplySentence {
        Sentence sentence1;
        Sentence sentence2;
    };

    // QuantifiedSentence EBNF Definition of exists and forall;
    // exists requires existential-preconditions
        // <gd> ::= (exists (<typed list (variable)>*) <gd>)
    // forall requires universal-preconditions
        // <gd> ::= (forall (<typed list (variable)>*) <gd>)
    struct QuantifiedSentence {
        std::string quantifier;
        TypedList<Variable> variables;
        Sentence sentence;
    };

    struct Constraint : x3::variant<Nil, EqualsSentence, NotEqualsSentence> {
        using base_type::base_type;
        using base_type::operator=;
    };

    // Constraints EBNF Definition:
        // <constraint-defs> ::= ()
        //    | <constraint-def>
        //    | (= <term> <term>)
    struct Constraints : x3::variant<Nil, Constraint, std::vector<Constraint>> {
        using base_type::base_type;
        using base_type::operator=;
    };

    // Abstract Tasks, decomposed by methods
    // Task EBNF Definition:
        // <task-def> ::= <task-symbol>
        //     :parameters (<typed list (variable)>)
        // <task-symbol> ::= <name>
    struct Task : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
    };

    // MTask is subtask without an ID. EBNF Definiton:
        // <subtask-def> ::= (<task-symbol> <term>*)
    struct MTask : x3::position_tagged {
        Name name;
        std::vector<Term> parameters;
    };

    // SubTaskWithId EBNF Definition:
        // <subtask-def> ::= (<subtask-id> (<task-symbol> <term>*))
    struct SubTaskWithId : x3::position_tagged {
        Name id;
        MTask subtask;
    };

    // SubTask EBNF Definition:
        // <subtask-def> ::= (<task-symbol> <term>*)
        //                 | (<subtask-id> (<task-symbol> <term>*))

    struct SubTask : x3::variant<MTask, SubTaskWithId> {
        using base_type::base_type;
        using base_type::operator=;
    };

    // SubTasks EBNF Definition:
        // <subtask-defs> ::= () | <subtask-def> | (and <subtask-def>+)
    struct SubTasks : x3::variant<Nil, SubTask, std::vector<SubTask>> {
        using base_type::base_type;
        using base_type::operator=;
    };

    // Ordering EBNF Definition:
        // <ordering_def> ::= (<subtask-id> "<" <subtask-id>)
    struct Ordering : x3::position_tagged {
        Name first;
        Name second;
    };

    // Orderings EBNF Definition:
        // <ordering-defs> ::= () | <ordering-def> | (and <ordering-def>+)
    struct Orderings : x3::variant<Nil, Ordering, std::vector<Ordering>> {
        using base_type::base_type;
        using base_type::operator=;
    };

    struct MethodSubTasks : x3::position_tagged {
        std::string ordering_kw;
        SubTasks subtasks;
    };

    // TaskNetwork EBNF Definition:
        // <tasknetwork-def> ::=
        //    [:[ordered-][sub]tasks <subtask-defs>]
        //    [:order[ing] <ordering-defs>]
        //    [:constraints <constraint-defs>]
    struct TaskNetwork : x3::position_tagged {
        std::optional<MethodSubTasks> subtasks;
        std::optional<Orderings> orderings;
        std::optional<Constraints> constraints;
    };

    // Method EBNF Definition:
        // (<method-def> ::=
        //     method <name>
        //     (<typed list (variable)>)
        //     (<task-symbol> <term>*)
        //     [:precondition <gd>]
        //     <tasknetwork-def>)
    struct Method : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
        MTask task;
        Sentence precondition;
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

    // Effect EBNF Definition:
        // <effect> ::= ()
        //            | (and <c-effect>*)
        //            | <c-effect>
    using Effect =
        boost::variant<Nil, boost::recursive_wrapper<AndCEffect>, CEffect>;

    // WhenCEffect EBNF Definition: requires conditional-effects
        // <c-effect> ::= (when <gd> <cond-effect>)
    struct WhenCEffect : x3::position_tagged {
        Sentence gd;
        CondEffect cond_effect;
    };

    // ForallCEffect EBNF Definition: requires conditional-effects
        // <c-effect> ::= (forall (<variable>*) <effect>)
    struct ForallCEffect : x3::position_tagged {
        std::vector<Variable> variables;
        Effect effect;
    };

    // AndCEffect EBNF Definition: <effect> ::= (and <c-effect>*)
    struct AndCEffect : x3::position_tagged {
        std::vector<CEffect> c_effects;
    };

    // Primitive Actions
    // Action EBNF Definition:
        // <action-def> ::= (:action
        //     <task-def>
        //     [:precondition <gd>]
        //     [:effects <effect>])
    struct Action : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
        Sentence precondition;
        Effect effect;
    };

    // Domain EBNF Definition:
        //  <domain> ::= (define (domain <name>)
        //      [<require-def>]
        //      [<types-def] ^(:typing)
        //      [<constants-def>]
        //      [<predicates-def>]
        //      <comp-task-def>*
        //      <method-def>*
        //      <action-def>*)
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

    // ProblemHTN EBNF Definition:
        // <p-htn> ::= (<p-class>
        //     [:parameters (<typed list (variable)>)]
        //     <tasknetwork-def>)

        // <p-class> ::= :htn
    struct ProblemHTN : x3::position_tagged {
        std::string problem_class;
        TypedList<Variable> parameters;
        TaskNetwork task_network;
    };

    using Init = std::vector<Literal<Name>>;

    // Problem EBNF Definition:
        // <problem> ::= (define (problem <name>)
        //     (:domain <name>)
        //     [<require-def>]
        //     [<p-object-declaration>]
        //     [<p-htn>]
        //     <p-int>
        //     [<p-goal>])
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
