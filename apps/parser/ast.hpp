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

        using TypedList = std::vector<Entity>;

        struct Action : x3::position_tagged {
            std::string name;
            TypedList parameters;
        };

        struct Domain : x3::position_tagged {
            std::string name;
            std::vector<std::string> requirements;
            TypedList types;
            std::vector<Action> actions;
        };

        using boost::fusion::operator<<;
    } // namespace ast
} // namespace client
