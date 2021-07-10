#pragma once

#include "../fol/Constant.h"
#include "../fol/Function.h"
#include "../fol/Predicate.h"
#include "../fol/Term.h"
#include "../fol/Variable.h"
#include "../fol/Literal.h"
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
    using fol::Literal;

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

    struct ConnectedSentence {
        std::string connector;
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
        TypedList<Variable> variables;
        Sentence sentence;
    };

    struct ForallSentence {
        TypedList<Variable> variables;
        Sentence sentence;
    };

    // Abstract Tasks
    struct Task : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
    };

/********************************* CURRENT WORK ******************************
// Partially-ordered subtasks. Ordering keyword gives these constraints. 
// However, in this method, this results in a totally-ordered method.
;;            (:method m-drive-to-via
;              :parameters (?li ?ld - site)
;              :task (get-to ?ld)
;              :subtasks 
;                (and (t1 (get-to ?li))
;                     (t2 (drive ?li ld)))
;              :ordering 
;                (and (t1 < t2)))
;            
// To Add Precondition before all other subtasks.
// Effects are not formally defined for any Methods.
;            (:method m-already-there
;              :parameters (?l - site)
;              :task (get-to ?l)
;              :precondition (tAt ?l)
;              :subtasks ())

// Constraints are not effects or preconditions!
// These are more intuitive and logical than using preconditions as
// constraints.
;            (:method m-direct
;              :parameters (?ls ?ls - site)
;              :task (get-to ?ld)
;              :constraints 
;                (not (= ?li ?ld))
;              :subtasks (drive ?ls ?d))

***********************/ 
// Totally-ordered methods use the keyword 'ordered-subtasks'
// Partially-ordered methods use the keyword 'subtasks'
    struct Method : x3::position_tagged {
        Name name;
        TypedList<Variable> parameters;
        Literal<Term> tasks;
//        Sentence constraints;//optional
        Sentence precondition; //optional
        Sentence osubtasks;// iff keyword ordered-subtasks
//        Sentence subtasks; //iff keyword subtasks

        /*  I am not sure if constraints should be a sentence ***/
    };
    
/******************************* END CURRENT WORK ******************************/

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
