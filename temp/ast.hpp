#pragma once

#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include <iostream>
#include <string>

namespace client {
    namespace ast {
        using Name = std::string;
        namespace x3 = boost::spirit::x3;

        struct Entity {
            Name name;
            Name type;
            Entity(const std::string name, const std::string type = "object")
                : name(name), type(type){};
        };

        struct Variable : Entity, x3::position_tagged {
            // Inherit all constructors of the Entity class
            using Entity::Entity;
            //Variable(const std::string name, const std::string type = "object")
                //: Entity(name, type){};
        };



        using Term = std::variant<Name, Variable>;

        template<class T>
        struct AtomicFormula {
            Name predicate;
            std::vector<T> args;
            bool is_negated;

            AtomicFormula() {};
            AtomicFormula(const Name predicate, const std::vector<T> args, bool is_negated=false)
                : predicate(predicate), args(args), is_negated(is_negated) {};
        };


        struct Action : x3::position_tagged {
            Name name;
            std::vector<Variable> parameters;
            std::vector<AtomicFormula<Variable>> precondition;
        };

        struct AtomicFormulaSkeleton : x3::position_tagged {
            Name predicate;
            std::vector<Variable> variables;
        };

        struct Domain : x3::position_tagged {
            Name name;
            std::vector<std::string> requirements;
            std::vector<Entity> types;
            std::vector<Entity> constants;
            std::vector<AtomicFormulaSkeleton> predicates;
            std::vector<Action> actions;
        };

        struct Problem : x3::position_tagged {
            Name name;// to just get name of problem
            Name probDomain;// for domain association
            std::vector<std::string> requireDomain;//for any problem requirements
            std::vector<Entity> objects;
        };//end problem struct

        using boost::fusion::operator<<;
    } // namespace ast
} // namespace client
