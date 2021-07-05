#pragma once
#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/utility/annotate_on_success.hpp>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "domain.hpp"
#include "error_handler.hpp"

namespace parser {
    using ast::Constant, ast::Variable, ast::PrimitiveType, ast::EitherType,
        ast::Type, ast::ImplicitlyTypedList, ast::ExplicitlyTypedList,
        ast::TypedList, ast::Name, ast::Term, ast::Literal, ast::Sentence, ast::Action;

    using boost::fusion::at_c;
    using x3::lexeme, x3::lit, x3::alnum, x3::_attr, x3::_val, x3::space,
        x3::eol, x3::rule, x3::symbols;

    auto const name =
        lexeme[!lit('-') >> +(char_ - '?' - '(' - ')' - ':' - space)];

    // Rules

    rule<class TRequirement, std::vector<Name>> const requirement =
        "requirement";
    auto const requirement_def = ':' >> name;

    rule<class TPredicate, Name> const predicate = "predicate";
    auto const predicate_def = name;

    rule<class TRequirements, std::vector<Name>> const requirements =
        "requirements";
    auto const requirements_def = '(' >> lit(":requirements") >> +requirement >>
                                  ')';

    rule<class TConstant, Constant> const constant = "constant";
    auto const constant_def = name;

    rule<class TVariable, Variable> const variable = "variable";
    auto const variable_def = '?' >> name;

    rule<class TPrimitiveType, PrimitiveType> const primitive_type =
        "primitive_type";
    auto const primitive_type_def = name;

    rule<class TEitherType, EitherType> const either_type = "either_type";
    auto const either_type_def = '(' >> lit("either") >> +primitive_type >> ')';

    rule<class TType, Type> const type = "type";
    auto const type_def = primitive_type | either_type;

    // Typed list of names
    rule<class TExplicitlyTypedListNames, ExplicitlyTypedList<Name>> const
        explicitly_typed_list_names = "explicitly_typed_list_names";
    auto const explicitly_typed_list_names_def = +name >> '-' >> type;

    rule<class TImplicitlyTypedListNames, ImplicitlyTypedList<Name>> const
        implicitly_typed_list_names = "implicitly_typed_list_names";
    auto const implicitly_typed_list_names_def = *name;

    rule<class TTypedListNames, TypedList<Name>> const typed_list_names =
        "typed_list_names";
    auto const typed_list_names_def =
        *explicitly_typed_list_names >> -implicitly_typed_list_names;

    BOOST_SPIRIT_DEFINE(explicitly_typed_list_names,
                        implicitly_typed_list_names,
                        typed_list_names);

    // Typed list of variables
    rule<class TExplicitlyTypedListVariables,
         ExplicitlyTypedList<Variable>> const explicitly_typed_list_variables =
        "explicitly_typed_list_variables";
    auto const explicitly_typed_list_variables_def = +variable >> '-' >> type;

    rule<class TImplicitlyTypedListVariables,
         ImplicitlyTypedList<Variable>> const implicitly_typed_list_variables =
        "implicitly_typed_list_variables";
    auto const implicitly_typed_list_variables_def = *variable;

    rule<class TTypedListVariables, TypedList<Variable>> const
        typed_list_variables = "typed_list_variables";
    auto const typed_list_variables_def =
        *explicitly_typed_list_variables >> -implicitly_typed_list_variables;

    BOOST_SPIRIT_DEFINE(explicitly_typed_list_variables,
                        implicitly_typed_list_variables,
                        typed_list_variables);

    // Atomic formula skeleton
    rule<class TAtomicFormulaSkeleton, ast::AtomicFormulaSkeleton> const
        atomic_formula_skeleton = "atomic_formula_skeleton";
    auto const atomic_formula_skeleton_def =
        '(' >> name >> typed_list_variables >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_skeleton);

    // Term
    rule<class TTerm, ast::Term> const term = "term";
    auto const term_def = constant | variable;
    BOOST_SPIRIT_DEFINE(term);

    // Atomic formula of terms
    rule<class TAtomicFormulaTerms, ast::AtomicFormula<ast::Term>> const
        atomic_formula_terms = "atomic_formula_terms";
    auto const atomic_formula_terms_def = '(' >> predicate >> *term >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_terms);

    // Literals of terms
    auto parse_negative_literal = [](auto& ctx) {
         _val(ctx).predicate = _attr(ctx).predicate;
         _val(ctx).args = _attr(ctx).args;
         _val(ctx).is_negative = true;
    };
    auto parse_positive_literal = [](auto& ctx) {
         _val(ctx).predicate = _attr(ctx).predicate;
         _val(ctx).args = _attr(ctx).args;
         _val(ctx).is_negative = false;
    };

    rule<class TLiteralTerms, ast::Literal<ast::Term>> const literal_terms =
                                 "literal_terms";
    auto const literal_terms_def =
        atomic_formula_terms[parse_positive_literal] | ('(' >> lit("not") >> atomic_formula_terms >> ')')[parse_negative_literal];
    BOOST_SPIRIT_DEFINE(literal_terms);

    // Nil
    rule<class TNil, ast::Nil> const nil = "nil";
    auto const nil_def = '(' >> lit(")");
    BOOST_SPIRIT_DEFINE(nil);

    rule<class TSentence, ast::Sentence> sentence = "sentence";


    struct connector_ : x3::symbols<std::string>
    {
        connector_()
        {
            add
                ("and"    , "and")
                ("or"    , "or")
            ;
        }

    } connector;


    rule<class TConnectedSentence, ast::ConnectedSentence> const connected_sentence =
                                  "connected_sentence";
    auto const connected_sentence_def = '('
                               >> connector
                               >> *sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(connected_sentence);


    rule<class TNotSentence, ast::NotSentence> const not_sentence =
                                  "not_sentence";
    auto const not_sentence_def = '('
                               >> lit("not")
                               >> sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(not_sentence);


    rule<class TImplySentence, ast::ImplySentence> const imply_sentence =
                                   "imply_sentence";
    auto const imply_sentence_def = '('
                                >> lit("imply")
                                >> sentence
                                >> sentence
                                >> ')';
    BOOST_SPIRIT_DEFINE(imply_sentence);


    rule<class TExistsSentence, ast::ExistsSentence> const exists_sentence =
                                   "exists_sentence";
    auto const exists_sentence_def = '('
                                >> lit("exists")
                                >> '('
                                >> typed_list_variables
                                >> ')'
                                >> sentence
                                >> ')';
    BOOST_SPIRIT_DEFINE(exists_sentence);


    rule<class TForallSentence, ast::ForallSentence> const forall_sentence =
                                   "forall_sentence";
    auto const forall_sentence_def = '('
                                >> lit("forall")
                                >> '('
                                >> typed_list_variables
                                >> ')'
                                >> sentence
                                >> ')';
    BOOST_SPIRIT_DEFINE(forall_sentence);

    auto const sentence_def = nil | literal_terms |
                              connected_sentence | not_sentence |
                              imply_sentence | exists_sentence | forall_sentence;
    BOOST_SPIRIT_DEFINE(sentence);


    // Typed Lists
    rule<class TTypes, TypedList<Name>> const types = "types";
    auto const types_def = '(' >> lit(":types") >> typed_list_names >> ')';
    BOOST_SPIRIT_DEFINE(types);

    rule<class TConstants, TypedList<Name>> const constants = "constants";
    auto const constants_def = '(' >> lit(":constants") >> typed_list_names >>
                               ')';
    BOOST_SPIRIT_DEFINE(constants);

    rule<class TPredicates, std::vector<ast::AtomicFormulaSkeleton>> const
        predicates = "predicates";
    auto const predicates_def = '(' >> lit(":predicates") >>
                                +atomic_formula_skeleton >> ')';
    BOOST_SPIRIT_DEFINE(predicates);


/***** Start ***** ***** ***** end current stuff ***** ***** ***** *****/
    struct TAction;

    rule<class TParameters, TypedList<Variable>> const parameters = "parameters";
    auto const parameters_def = lit(":parameters")
                               >> '('
                               >> typed_list_variables
                               >> ')';
    BOOST_SPIRIT_DEFINE(parameters);

    rule<class TPrecondition, ast::Sentence> const precondition = "precondition";
    auto const precondition_def = '(' >> lit(":precondition") >> sentence >> ')';
    BOOST_SPIRIT_DEFINE(precondition);

    rule<class TAction, ast::Action> const action = "action";
    auto const action_def = '('
                            >> lit(":action")
                            >> name
                            >> -parameters //optional for now
                            >> -precondition
                            >> ')';
    BOOST_SPIRIT_DEFINE(action);

/***** ***** ***** ***** end current stuff ***** ***** ***** *****/






    rule<class TDomain, ast::Domain> const domain = "domain";
    auto const domain_def = '(' >> lit("define") >> '('
                         >> lit("domain")
                         >> name >> ')'
                         >> requirements
                         >> -types
                         >> -constants
                         >> -predicates 
                         // 3 errors when this is included using -+*or alone
                         // >> -action
                         >> ')';
    BOOST_SPIRIT_DEFINE(domain);

    rule<class TObjects, TypedList<Name>> const objects = "objects";
    auto const objects_def = '(' >> lit(":objects") >> typed_list_names >> ')';
    BOOST_SPIRIT_DEFINE(objects);

    rule<class TInit, Literal<Term>> const init = "init";
    auto const init_def = '(' >> lit(":init") >> literal_terms >> ')';
    BOOST_SPIRIT_DEFINE(init);

    rule<class TGoal, Sentence> const goal = "goal";
    auto const goal_def = '(' >> lit(":goal") >> sentence >> ')';
    BOOST_SPIRIT_DEFINE(goal);

    rule<class TProblem, ast::Problem> const problem = "problem";
    auto const problem_def = '('
                          >> lit("define")
                          >> '(' >> lit("problem") >> name >> ')'
                          >> '(' >> lit(":domain") >> name >> ')'
                          >> -requirements
                          >> -objects
                          >> init
                          >> goal
                          >> ')';
    BOOST_SPIRIT_DEFINE(problem);


    BOOST_SPIRIT_DEFINE(constant,
                        variable,
                        primitive_type,
                        either_type,
                        type,
                        predicate,
                        requirement,
                        requirements);

} // namespace parser

parser::constant_type constant() { return parser::constant; }
parser::variable_type variable() { return parser::variable; }
parser::primitive_type_type primitive_type() { return parser::primitive_type; }
parser::either_type_type either_type() { return parser::either_type; }
parser::type_type type() { return parser::type; }

parser::typed_list_names_type typed_list_names() {
    return parser::typed_list_names;
}
parser::typed_list_variables_type typed_list_variables() {
    return parser::typed_list_variables;
}
parser::atomic_formula_skeleton_type atomic_formula_skeleton() {
    return parser::atomic_formula_skeleton;
}
parser::atomic_formula_terms_type atomic_formula_terms() {
    return parser::atomic_formula_terms;
}
parser::literal_terms_type literal_terms() { return parser::literal_terms; }

parser::sentence_type sentence() { return parser::sentence; }
parser::requirements_type requirements() { return parser::requirements; }
parser::domain_type domain() { return parser::domain; }
parser::problem_type problem() { return parser::problem; }
parser::action_type action() { return parser::action; }
