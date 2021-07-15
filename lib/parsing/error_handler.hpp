#pragma once
#include "api.hpp"

#include <boost/spirit/home/x3/support/ast/position_tagged.hpp>
#include <boost/spirit/home/x3/support/utility/error_reporting.hpp>

#include <map>

namespace parser {
    namespace x3 = boost::spirit::x3;

    ////////////////////////////////////////////////////////////////////////////
    //  Our error handler
    ////////////////////////////////////////////////////////////////////////////
    template <typename Iterator>
    using error_handler = x3::error_handler<Iterator>;

    struct ErrorHandlerBase {
        ErrorHandlerBase();

        // Declare template error handler function
        template <class Iterator, class Exception, class Context>
        x3::error_handler_result on_error(Iterator& first,
                                          Iterator const& last,
                                          Exception const& x,
                                          Context const& context);

        std::map<std::string, std::string> id_map;
    };

    ////////////////////////////////////////////////////////////////////////////
    // Implementation
    ////////////////////////////////////////////////////////////////////////////

    inline ErrorHandlerBase::ErrorHandlerBase() {
        id_map["domain"] = "Domain";
        id_map["problem"] = "Problem";
        id_map["action"] = "Action";
        id_map["task"] = "Task";
        id_map["method"] = "Method";
        id_map["requirements"] = "Requirements";
        id_map["typed_list"] = "TypedList";
        id_map["literal_terms"] = "Literal<Term>";
    }

    template <class Iterator, class Exception, class Context>
    inline x3::error_handler_result
    ErrorHandlerBase::on_error(Iterator& first,
                               Iterator const& last,
                               Exception const& x,
                               Context const& context) {
        std::string which = x.which();

        auto iter = id_map.find(which);
        if (iter != id_map.end()) {
            which = iter->second;
        }

        std::string message = "Error! Expecting: " + which + " here:";
        auto& error_handler = x3::get<x3::error_handler_tag>(context).get();
        error_handler(x.where(), message);
        return x3::error_handler_result::fail;
    }
} // namespace parser
