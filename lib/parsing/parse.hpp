#pragma once

#include "config.hpp"
#include "error_handler.hpp"
#include <boost/throw_exception.hpp>
#include <exception>
#include <iostream>
#include <string>

template <class T, class U> T parse(std::string storage, U parser) {
    using parser::error_handler_tag;
    namespace x3 = boost::spirit::x3;
    std::string::const_iterator iter = storage.begin();
    std::string::const_iterator end = storage.end();
    parser::ErrorHandlerType error_handler(iter, end, std::cerr);
    T object;
    auto const error_handling_parser =
        x3::with<x3::error_handler_tag>(std::ref(error_handler))[parser];
    bool r =
        phrase_parse(iter, end, error_handling_parser, parser::skipper, object);
    if (r) {
        if (iter != end) {
            error_handler(iter, "Error! Expecting end of input here: ");
        }
    }
    else {
        BOOST_THROW_EXCEPTION(std::runtime_error("Parsing error!"));
    }
    return object;
}
