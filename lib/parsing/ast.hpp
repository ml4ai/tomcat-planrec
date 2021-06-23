#pragma once

#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include <boost/variant/recursive_variant.hpp>
#include <iostream>
#include <string>
#include <unordered_set>

namespace ast {
    using Name = std::string;
    namespace x3 = boost::spirit::x3;

    struct Constant {
        Name name;
    };

    struct Variable : x3::position_tagged {
        Name name;
    };

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

    using Type = x3::variant<PrimitiveType, EitherType>;

    template <class T> using ImplicitlyTypedList = std::vector<T>;

    template <class T> struct ExplicitlyTypedList {
        std::vector<T> entries;
        Type type;
    };

    template <class T> struct TypedList {
        std::vector<ExplicitlyTypedList<T>> explicitly_typed_lists;
        boost::optional<ImplicitlyTypedList<T>> implicitly_typed_list;
    };

    struct Predicate {
        Name name;
    };

    struct AtomicFormulaSkeleton : x3::position_tagged {
        Predicate predicate;
        TypedList<Variable> args;
    };

    // struct Action : x3::position_tagged {
    // Name name;
    // std::vector<Variable> parameters;
    //};

    // using Term = std::variant<Name, Variable>;

    // template <class T> struct AtomicFormula {
    // Name predicate;
    // std::vector<T> args;
    //};

    // struct GoalDescription;

    // struct GoalDescriptionValue
    //: x3::variant<std::string, x3::forward_ast<GoalDescription>> {
    // using base_type::base_type;
    // using base_type::operator=;
    //};

    // struct GoalDescription {
    // std::vector<GoalDescriptionValue> entries;
    //};

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
        Name domain_name;                           // for domain association
        std::vector<std::string> requirements; // for any problem requirements
        TypedList<Name> objects;
    }; // end problem struct

    using boost::fusion::operator<<;
} // namespace ast
