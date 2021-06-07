#pragma once

#include <boost/fusion/include/io.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include <iostream>
#include <string>

namespace client {
    namespace ast {
        using name = std::string;
        namespace x3 = boost::spirit::x3;

        struct Entity {
            std::string name;
            std::string type;
            Entity(const std::string name, const std::string type = "object")
                : name(name), type(type){};
        };

        struct Variable : Entity, x3::position_tagged {
            // Inherit all constructors of the Entity class
            using Entity::Entity;
        };

        struct Action : x3::position_tagged {
            std::string name;
            std::vector<Entity> parameters;
        };


        struct AtomicFormulaSkeleton : x3::position_tagged {
            std::string predicate;
            std::vector<Variable> variables;
        };

        struct Domain : x3::position_tagged {
            std::string name;
            std::vector<std::string> requirements;
            std::vector<Entity> types;
            std::vector<Entity> constants;
            std::vector<AtomicFormulaSkeleton> predicates;
            std::vector<Action> actions;
        };

        using boost::fusion::operator<<;
    } // namespace ast
} // namespace client
