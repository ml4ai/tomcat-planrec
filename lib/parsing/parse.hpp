#pragma once

#include <string>
#include <iostream>
#include "config.hpp"
#include "error_handler.hpp"
#include <exception>

template <class T, class U> T parse(std::string storage, U parser) {
    using parser::error_handler_tag, parser::error_handler_type;
    std::string::const_iterator iter = storage.begin();
    std::string::const_iterator end = storage.end();
    error_handler_type error_handler(iter, end, std::cerr);
    T object;
    auto const error_handling_parser =
        boost::spirit::x3::with<error_handler_tag>(ref(error_handler))[parser];
    bool r =
        phrase_parse(iter, end, error_handling_parser, parser::skipper, object);
    if (!(r && iter == end)) {
        error_handler(iter, "Error!");
        throw std::runtime_error("Parsing error!");
    }
    return object;
}

