#pragma once
#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3.hpp>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "domain.hpp"

namespace client
{
    ///////////////////////////////////////////////////////////////////////////////
    //  Our domain parser definition
    ///////////////////////////////////////////////////////////////////////////////
    namespace parser
    {
        using boost::fusion::at_c;
        using client::ast::Entity;
        using x3::lexeme, x3::lit, x3::alnum, x3::_attr,
            x3::_val, x3::space, x3::eol;

        ///////////////////////////////////////////////////////////////////////
        //  Our annotation handler
        ///////////////////////////////////////////////////////////////////////

        // tag used to get the position cache from the context
        struct position_cache_tag;

        struct annotate_position
        {
            template <typename T, typename Iterator, typename Context>
            inline void on_success(Iterator const& first, Iterator const& last
            , T& ast, Context const& context)
            {
                auto& position_cache = x3::get<position_cache_tag>(context).get();
                position_cache.annotate(ast, first, last);
            }
        };


        auto const name = lexeme[+(char_ - '?' - '(' - ')' - ':' - space)];
        auto const requirement = ':' >> name;
        auto const variable = '?' >> name;
        auto const require_def =
            '('
            >> lit(":requirements")
            >> +requirement
            >> ')';
        auto const types_def = '(' >> lit(":types") >> +name >> ')';

        x3::rule<class TTypedList, ast::TypedList> const typed_list =
            "typed_list";
        x3::rule<class TAction, ast::Action> const action = "action";
        x3::rule<class TDomain, ast::Domain> const domain = "domain";

        auto add_implicitly_typed_entity = [](auto& ctx) {
            _val(ctx).push_back(Entity(_attr(ctx)));
        };

        auto add_explicitly_typed_entities = [](auto& ctx) {
            auto dq = _attr(ctx);
            std::vector<std::string> names = at_c<0>(dq);
            std::string type = at_c<1>(dq);

            for (std::string& name : names) {
                Entity entity = Entity(name, type);
                _val(ctx).push_back(entity);
            }
        };

        auto const implicitly_typed_list =
            *variable[add_implicitly_typed_entity];
        auto const explicitly_typed_list =
            (+variable >> '-' >> name)[add_explicitly_typed_entities];
        auto const typed_list_def =
            *explicitly_typed_list >> -implicitly_typed_list;

        auto const action_def =
            '('
            >> lit(":action")
            >> name
            >> lit(":parameters")
            >> '(' >> typed_list >> ')'
            >> ')';

        auto const domain_def = '(' >> lit("define") >> '(' >>
                                lit("domain") >> name >> ')' >> -require_def >>
                                -types_def >> +action >> ')';

        BOOST_SPIRIT_DEFINE(typed_list, action, domain);


        // Set up the skip parser so that it can be used from parser.cpp
        using skipper_type=decltype(skipper);
        using phrase_context_type = x3::phrase_parse_context<skipper_type>::type;

    }

    parser::domain_type domain()
    {
        return parser::domain;
    }
}
