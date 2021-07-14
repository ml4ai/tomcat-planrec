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
    using fol::Literal;
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
    struct ExistsSentence;
    struct ForallSentence;

    using Sentence = boost::variant<Nil,
                                    Literal<Term>,
                                    boost::recursive_wrapper<ConnectedSentence>,
                                    boost::recursive_wrapper<NotSentence>,
                                    boost::recursive_wrapper<ImplySentence>,
                                    boost::recursive_wrapper<ExistsSentence>,
                                    boost::recursive_wrapper<ForallSentence>>;

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

    struct ExistsSentence : x3::position_tagged {
        TypedList<Variable> variables;
        Sentence sentence;
    };

    struct ForallSentence : x3::position_tagged {
        TypedList<Variable> variables;
        Sentence sentence;
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

    using SubTask = boost::variant<MTask, SubTaskWithId>;

    using SubTasks = boost::variant<Nil, SubTask, std::vector<SubTask>>;

    struct Ordering : x3::position_tagged {
        Name first;
        Name second;
    };

    using Orderings = boost::variant<Nil, Ordering, std::vector<Ordering>>;

    struct MethodSubTasks : x3::position_tagged {
        std::string ordering_kw;
        SubTasks subtasks;
    };

    struct TaskNetwork : x3::position_tagged {
        MethodSubTasks subtasks;
        Orderings orderings;
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

    // Primitive Actions
    struct Action : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
        Sentence precondition;
        Sentence effect;
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

    struct Problem : x3::position_tagged {
        Name name;
        Name domain_name;
        std::vector<std::string> requirements;
        TypedList<Name> objects;
        Literal<Term> init;
        Sentence goal;
    };

    using boost::fusion::operator<<;
} // namespace ast
