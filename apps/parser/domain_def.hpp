#pragma once
#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/utility/annotate_on_success.hpp>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "error_handler.hpp"
#include "domain.hpp"

namespace client
{
    ///////////////////////////////////////////////////////////////////////////////
    //  Our domain parser definition
    ///////////////////////////////////////////////////////////////////////////////
    namespace parser
    {
        using boost::fusion::at_c;
        using ast::Entity, ast::Variable, ast::Action, ast::Domain, ast::AtomicFormulaSkeleton;
        using x3::lexeme, x3::lit, x3::alnum, x3::_attr,
            x3::_val, x3::space, x3::eol, x3::rule;

        auto const name = lexeme[!lit('-') >> +(char_ - '?' - '(' - ')' - ':' - space)];
        auto const requirement = ':' >> name;
        auto const variable = '?' >> name;

        // Rule IDs
        struct Entities;
        struct Variables;
        struct TAction;
        struct TDomain;

        // Rules
        rule<class Entities, std::vector<Entity>> const typed_list_names = "typed_list_names";
        rule<class Variables, std::vector<Variable>> const typed_list_variables = "typed_list_variables";
        rule<class TAtomicFormulaSkeleton, AtomicFormulaSkeleton> const atomic_formula_skeleton = "atomic_formula_skeleton";
        rule<class TAction, Action> const action = "action";
        rule<class TDomain, Domain> const domain = "domain";

        // Grammar
        auto const primitive_type = name;

        // TODO We do not handle 'either' types
        //auto const type = primitive_type | '(' >> lit("either") >>  +primitive_type >> ')';

        auto const type = primitive_type;

        template<class T>
        auto add_implicitly_typed_entity = [](auto& ctx) {
            _val(ctx).push_back(T(_attr(ctx)));
        };

        template<class T>
        auto add_explicitly_typed_entities = [](auto& ctx) {
            auto dq = _attr(ctx);
            std::vector<std::string> names = at_c<0>(dq);
            std::string type = at_c<1>(dq);

            for (std::string& name : names) {
                T entity = T(name, type);
                _val(ctx).push_back(entity);
            }
        };


        template<class U, class T> auto typed_list(T parser) {
            auto const implicitly_typed_list =
                *parser[add_implicitly_typed_entity<U>];
            auto const explicitly_typed_list =
                (+parser >> '-' >> name)[add_explicitly_typed_entities<U>];
            auto const typed_list_def =
                *explicitly_typed_list >> -implicitly_typed_list;
            return  typed_list_def;
        }


        auto const typed_list_names_def = typed_list<Entity>(name);
        auto const typed_list_variables_def = typed_list<Variable>(variable);

        auto const parameters_def = lit(":parameters") >> '(' >> typed_list_variables >> ')';

        auto const action_symbol = name;

        // TODO extend definitions of effect and GD
        auto const effect = ('(' >> lit(")"));
        auto const GD = ('(' >> lit(")"));

        auto const action_def_body = 
            -(lit(":precondition") >> GD)
            >> -(lit(":effect") >> effect);

        // Actions
        auto const action_def =
            '('
            >> lit(":action")
            >> action_symbol
            >> parameters_def 
            >> ')'
            ;



        // TODO Predicates
        auto const structure_def = action_def;
        auto const predicate = name;
        auto const atomic_formula_skeleton_def = '(' >> predicate >> typed_list_variables >> ')';
        auto const predicates_def = '(' >> lit(":predicates") >> +atomic_formula_skeleton >> ')';

        auto const constants_def = '(' >> lit(":constants") >> typed_list_names >> ')';
        auto const types_def = '(' >> lit(":types") >> typed_list_names >> ')';
        auto const require_def = '(' >> lit(":requirements") >> +requirement >> ')';

        auto const domain_def = 
            '(' >> lit("define") >> '(' >> lit("domain") >> name >> ')'
            >> -require_def
            >> -types_def
            >> -constants_def
            >> -predicates_def
            >> *structure_def
            >> ')'
            ;

        BOOST_SPIRIT_DEFINE(typed_list_names, typed_list_variables, atomic_formula_skeleton, action, domain);

        // Annotation and error handling
        struct Entities : x3::annotate_on_success, error_handler_base {};
        struct Variables : x3::annotate_on_success, error_handler_base {};
        struct TAction: x3::annotate_on_success, error_handler_base {};
        struct TDomain: x3::annotate_on_success, error_handler_base {};
    }

    parser::domain_type domain() {
        return parser::domain;
    }
}
