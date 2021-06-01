#pragma once

#include <boost/spirit/home/x3/support/ast/variant.hpp>
#include <iostream>
#include <string>

namespace client {
    namespace ast {
        using name = std::string;

        struct Entity {
            std::string name;
            std::string type;
            Entity(const std::string name, const std::string type = "object")
                : name(name), type(type){};
        };

        using TypedList = std::vector<Entity>;

        struct Action {
            std::string name;
            TypedList parameters;
        };

        struct Domain {
            std::string name;
            std::vector<std::string> requirements;
            std::vector<std::string> types;
            std::vector<Action> actions;
        };
    } // namespace ast
} // namespace client
