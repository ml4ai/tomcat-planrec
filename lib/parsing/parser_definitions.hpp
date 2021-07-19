#pragma once
#include <boost/config/warning_disable.hpp>
#include <boost/spirit/home/x3.hpp>
#include <boost/spirit/home/x3/support/utility/annotate_on_success.hpp>

#include "ast.hpp"
#include "ast_adapted.hpp"
#include "parser_definitions.hpp"
#include "error_handler.hpp"

namespace parser {
    using namespace ast;

    using boost::fusion::at_c;
    using x3::lexeme, x3::lit, x3::alnum, x3::_attr, x3::_val, x3::space,
        x3::eol, x3::rule, x3::symbols;

    auto const name =
        lexeme[!lit('-') >> +(char_ - '?' - '(' - ')' - ':' - space)];


    // Rules
    rule<class TRequirement, std::vector<Name>> const requirement =
        "requirement";
    auto const requirement_def = ':' >> name;
    BOOST_SPIRIT_DEFINE(requirement);
    struct TRequirement : x3::annotate_on_success {};

    rule<class TPredicate, Name> const predicate = "predicate";
    auto const predicate_def = name;
    BOOST_SPIRIT_DEFINE(predicate);
    struct TPredicate : x3::annotate_on_success {};

    rule<class TRequirements, std::vector<Name>> const requirements =
        "requirements";
    auto const requirements_def = '(' >> lit(":requirements") >> +requirement >>
                                  ')';
    BOOST_SPIRIT_DEFINE(requirements);
    struct TRequirements : x3::annotate_on_success {};

    rule<class TConstant, Constant> const constant = "constant";
    auto const constant_def = name;
    BOOST_SPIRIT_DEFINE(constant);
    struct TConstant : x3::annotate_on_success {};

    rule<class TVariable, Variable> const variable = "variable";
    auto const variable_def = '?' > name;
    BOOST_SPIRIT_DEFINE(variable);
    struct TVariable : x3::annotate_on_success {};

    rule<class TPrimitiveType, PrimitiveType> const primitive_type =
        "primitive_type";
    auto const primitive_type_def = name;
    BOOST_SPIRIT_DEFINE(primitive_type);
    struct TPrimitiveType : x3::annotate_on_success {};

    rule<class TEitherType, EitherType> const either_type = "either_type";
    auto const either_type_def = '(' >> lit("either") >> +primitive_type >> ')';
    BOOST_SPIRIT_DEFINE(either_type);
    struct TEitherType : x3::annotate_on_success {};

    rule<class TType, Type> const type = "type";
    auto const type_def = primitive_type | either_type;
    BOOST_SPIRIT_DEFINE(type);
    struct TType : x3::annotate_on_success {};

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
    struct TExplicitlyTypedListNames : x3::annotate_on_success {};
    struct TImplicitlyTypedListNames : x3::annotate_on_success {};
    struct TTypedListNames : x3::annotate_on_success {};

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

    struct TExplicitlyTypedListVariables : x3::annotate_on_success {};
    struct TImplicitlyTypedListVariables : x3::annotate_on_success {};
    struct TTypedListVariables : x3::annotate_on_success {};

    // Atomic formula skeleton
    rule<class TAtomicFormulaSkeleton, AtomicFormulaSkeleton> const
        atomic_formula_skeleton = "atomic_formula_skeleton";
    auto const atomic_formula_skeleton_def =
        '(' >> name >> typed_list_variables >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_skeleton);
    struct TAtomicFormulaSkeleton : x3::annotate_on_success {};

    // Term
    rule<class TTerm, Term> const term = "term";
    auto const term_def = constant | variable;
    BOOST_SPIRIT_DEFINE(term);
    struct TTerm : x3::annotate_on_success {};

    // Atomic formula of terms
    rule<class TAtomicFormulaTerms, AtomicFormula<Term>> const
        atomic_formula_terms = "atomic_formula_terms";
    auto const atomic_formula_terms_def = '(' >> predicate >> *term >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_terms);
    struct TAtomicFormulaTerms: x3::annotate_on_success {};

    // Literals of terms
    rule<class TLiteralTerms, Literal<Term>> const literal_terms =
                                 "literal_terms";
    auto const literal_terms_def = atomic_formula_terms;
    BOOST_SPIRIT_DEFINE(literal_terms);
    struct TLiteralTerms: x3::annotate_on_success {};

    // Negative literals
    auto parse_negative_literal = [](auto& ctx) {
          _val(ctx).predicate = _attr(ctx).predicate;
          _val(ctx).args = _attr(ctx).args;
          _val(ctx).is_negative = true;
    };

    rule<class TNegativeLiteralTerms, Literal<Term>> const negative_literal_terms = "negative_literal_terms";
    auto const negative_literal_terms_def = ('(' >> lit("not") >> literal_terms >> ')')[parse_negative_literal];
    BOOST_SPIRIT_DEFINE(negative_literal_terms);
    struct TNegativeLiteralTerms: x3::annotate_on_success {};



    // Nil
    rule<class TNil, Nil> const nil = "nil";
    auto const nil_def = '(' >> lit(")");
    BOOST_SPIRIT_DEFINE(nil);
    struct TNil: x3::annotate_on_success {};

    rule<class TSentence, Sentence> sentence = "sentence";

    // Connectors (and/or)
    struct connector_ : x3::symbols<std::string> {
        connector_() {
            add
                ("and", "and")
                ("or" , "or")
            ;
        }
    } connector;


    rule<class TConnectedSentence, ConnectedSentence> const connected_sentence =
                                  "connected_sentence";
    auto const connected_sentence_def = '('
                               >> connector
                               >> *sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(connected_sentence);
    struct TConnectedSentence: x3::annotate_on_success {};


    rule<class TNotSentence, NotSentence> const not_sentence =
                                  "not_sentence";
    auto const not_sentence_def = '('
                               >> lit("not")
                               >> sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(not_sentence);
    struct TNotSentence: x3::annotate_on_success {};


    rule<class TImplySentence, ImplySentence> const imply_sentence =
                                   "imply_sentence";
    auto const imply_sentence_def = ('(' >> lit("imply"))
                                    > sentence
                                    > sentence
                                    > ')';
    BOOST_SPIRIT_DEFINE(imply_sentence);
    struct TImplySentence: x3::annotate_on_success {};

    // Quantifier (exists/forall)
    struct quantifier_ : x3::symbols<std::string> {
        quantifier_() {
            add
                ("exists", "exists")
                ("forall" , "forall")
            ;
        }
    } quantifier;

    rule<class TQuantifiedSentence, QuantifiedSentence> const quantified_sentence =
                                   "quantified_sentence";
    auto const quantified_sentence_def = '('
                               >> quantifier
                               >> '('
                               >> typed_list_variables
                               >> ')'
                               >> sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(quantified_sentence);
    struct TQuantifiedSentence: x3::annotate_on_success {};


    auto const sentence_def =
        nil
        | literal_terms
        | connected_sentence
        | not_sentence
        | imply_sentence
        | quantified_sentence
        ;
    BOOST_SPIRIT_DEFINE(sentence);
    struct TSentence : x3::annotate_on_success {};

    // <p-effect>
    rule<class TPEffect, Literal<Term>> const p_effect = "p_effect";
    auto const p_effect_def = literal_terms | negative_literal_terms;
    BOOST_SPIRIT_DEFINE(p_effect);
    struct TPEffect: x3::annotate_on_success {};

    // <cond-effect>
    rule<class TCondEffect, CondEffect> const cond_effect = "cond_effect";
    auto const cond_effect_def = p_effect | '(' >> lit("and") >> *p_effect >> ')';
    BOOST_SPIRIT_DEFINE(cond_effect);
    struct TCondEffect: x3::annotate_on_success {};

    // <effect and <c-effect>
    rule<class TEffect, Effect> const effect = "effect";
    rule<class TCEffect, CEffect> const c_effect = "c_effect";

    rule<class TForallCEffect, ForallCEffect> const forall_c_effect = "forall_c_effect";
    auto const forall_c_effect_def = ('(' >> lit("forall")) > '(' >> *variable >> ')' >> effect > ')';

    rule<class TAndCEffect, AndCEffect> const and_c_effect = "and_c_effect";
    auto const and_c_effect_def = ('(' >> lit("and")) > *c_effect > ')';

    rule<class TWhenCEffect, WhenCEffect> const when_c_effect = "when_c_effect";
    auto const when_c_effect_def = ('(' >> lit("when")) > sentence > cond_effect >> ')';

    auto const c_effect_def = forall_c_effect | when_c_effect | p_effect;
          
    auto const effect_def = 
        nil
        | and_c_effect 
        | c_effect;

    BOOST_SPIRIT_DEFINE(forall_c_effect);
    BOOST_SPIRIT_DEFINE(and_c_effect);
    BOOST_SPIRIT_DEFINE(when_c_effect);
    BOOST_SPIRIT_DEFINE(c_effect);
    BOOST_SPIRIT_DEFINE(effect);
    //struct TEffect: x3::annotate_on_success {};
    //struct TCEffect: x3::annotate_on_success {};


    // Typed Lists
    rule<class TTypes, TypedList<Name>> const types = "types";
    auto const types_def = ('(' >> lit(":types"))
                               > typed_list_names
                               > ')';
    BOOST_SPIRIT_DEFINE(types);
    struct TTypes: x3::annotate_on_success {};

    rule<class TConstants, TypedList<Name>> const constants = "constants";
    auto const constants_def = ('(' >> lit(":constants"))
                               > typed_list_names
                               > ')';
    BOOST_SPIRIT_DEFINE(constants);
    struct TConstants : x3::annotate_on_success {};

    rule<class TPredicates, std::vector<AtomicFormulaSkeleton>> const
        predicates = "predicates";
    auto const predicates_def = ('(' >> lit(":predicates"))
                               > +atomic_formula_skeleton > ')';
    BOOST_SPIRIT_DEFINE(predicates);
    struct TPredicates: x3::annotate_on_success {};

    rule<class TPrecondition, Sentence> const precondition = "precondition";
    auto const precondition_def = lit(":precondition")
                               > sentence;
    BOOST_SPIRIT_DEFINE(precondition);
    struct TPrecondition: x3::annotate_on_success {};

    rule<class TParameters, TypedList<Variable>> const parameters = "parameters";
    auto const parameters_def = lit(":parameters")
                               > '('
                               > typed_list_variables
                               > ')';
    BOOST_SPIRIT_DEFINE(parameters);
    struct TParameters: x3::annotate_on_success {};

    rule<class TTask, Task> const task = "task";
    auto const task_def = name >> parameters;
    BOOST_SPIRIT_DEFINE(task);
    struct TTask: x3::annotate_on_success {};


    // Abstract Tasks
    rule<class TAbstractTask, Task> const abstract_task = "abstract_task";
    auto const abstract_task_def = ('(' >> lit(":task")) > task >> ')';
    BOOST_SPIRIT_DEFINE(abstract_task);
    struct TAbstractTask: x3::annotate_on_success {};


    rule<class TTaskSymbolWithTerms, MTask> const task_symbol_with_terms = "task_symbol_with_terms";
    auto const task_symbol_with_terms_def = '(' >> name >> *term >> ')';
    BOOST_SPIRIT_DEFINE(task_symbol_with_terms);
    struct TTaskSymbolWithTerms: x3::annotate_on_success {};

    // Methods used to decompose abstract tasks into primitive actions
    // task as defined in Method struct != task defined in task struct
    // mtask refers to task definition found within a method:
    rule<class TMTask, MTask> const mtask = "mtask";
    auto const mtask_def = lit(":task") > task_symbol_with_terms;
    BOOST_SPIRIT_DEFINE(mtask);
    struct TMTask: x3::annotate_on_success {};

    rule<class TSubTaskWithId, SubTaskWithId> const subtask_with_id = "subtask_with_id";
    auto const subtask_with_id_def = '(' >> name >> task_symbol_with_terms >> ')';
    BOOST_SPIRIT_DEFINE(subtask_with_id);
    struct TSubTaskWithId: x3::annotate_on_success {};

    rule<class TSubTask, SubTask> const subtask = "subtask";
    auto const subtask_def = task_symbol_with_terms | subtask_with_id;
    BOOST_SPIRIT_DEFINE(subtask);
    struct TSubTask: x3::annotate_on_success {};

    rule<class TSubTasks, SubTasks> const subtasks = "subtasks";
    auto const subtasks_def = nil | subtask | '(' >> lit("and") >> +subtask >> ')';
    BOOST_SPIRIT_DEFINE(subtasks);
    struct TSubTasks: x3::annotate_on_success {};

    rule<class TOrdering, Ordering> const ordering = "ordering";
    auto const ordering_def = '(' >> name >> '<' >> name >> ')';
    BOOST_SPIRIT_DEFINE(ordering);
    struct TOrdering: x3::annotate_on_success {};

    rule<class TOrderings, Orderings> const orderings = "orderings";
    auto const orderings_def = nil | ordering | '(' >> lit("and") >> +ordering >> ')';
    BOOST_SPIRIT_DEFINE(orderings);
    struct TOrderings: x3::annotate_on_success {};

    rule<class TTaskNetworkOrderings, Orderings> const task_network_orderings = "task_network_orderings";
    auto const task_network_orderings_def = lit(":ordering") > orderings;
    BOOST_SPIRIT_DEFINE(task_network_orderings);
    struct TTaskNetworkOrderings: x3::annotate_on_success {};

    // Ordering keyword
    struct ordering_kw_ : x3::symbols<std::string> {
        ordering_kw_() {
            add
                ("tasks", "tasks")
                ("subtasks" , "subtasks")
                ("ordered-tasks" , "ordered-tasks")
                ("ordered-subtasks" , "ordered-subtasks")
            ;
        }
    } ordering_kw;

    rule<class TMethodSubTasks, MethodSubTasks> const method_subtasks = "method_subtasks";
    auto const method_subtasks_def = ':' >> ordering_kw >> subtasks;
    BOOST_SPIRIT_DEFINE(method_subtasks);
    struct TMethodSubTasks : x3::annotate_on_success {};

    rule<class TEqualsSentence, EqualsSentence> const equals_sentence =
                                   "equals_sentence";
    auto const equals_sentence_def = ('(' >> lit("="))
                                 > term
                                 > term
                                 > ')';
    BOOST_SPIRIT_DEFINE(equals_sentence);
    struct TEqualsSentence : x3::annotate_on_success {};

    rule<class TNotEqualsSentence, NotEqualsSentence> const not_equals_sentence =
                                   "not_equals_sentence";
    auto const not_equals_sentence_def = ('('
                               >> lit("not"))
                               > equals_sentence
                               > ')';
    BOOST_SPIRIT_DEFINE(not_equals_sentence);
    struct TNotEqualsSentence: x3::annotate_on_success {};

    rule<class TConstraint, Constraint> const constraint = "constraint";
    auto const constraint_def = nil | not_equals_sentence | equals_sentence;
    BOOST_SPIRIT_DEFINE(constraint);
    struct TConstraint : x3::annotate_on_success {};

    rule<class TConstraints, Constraints> const constraints = "constraints";
    auto const constraints_def = nil | constraint | '(' >> lit("and") >> +constraint >> ')';
    BOOST_SPIRIT_DEFINE(constraints);
    struct TConstraints : x3::annotate_on_success {};

    rule<class TTaskNetwork, TaskNetwork> const task_network = "task_network";
    auto const task_network_def = -method_subtasks
                               >> -task_network_orderings
                               >> -(lit(":constraints") > constraints);
    BOOST_SPIRIT_DEFINE(task_network);
    struct TTaskNetwork: x3::annotate_on_success {};

    rule<class TMethod, Method> const method = "method";
    auto const method_def = ('(' >> lit(":method"))
                                > name
                                > parameters
                                > mtask // one task
                                >> -precondition
                                > task_network
                                > ')';
    BOOST_SPIRIT_DEFINE(method);
    struct TMethod: x3::annotate_on_success {};


    // Primitive actions

    // Note: There is a typo in section 4 of the HDDL paper
    // https://arxiv.org/pdf/1911.05499.pdf - in the specification of actions,
    // it should be ':effect' instead of ':effects' (line 44 of their listing).
    rule<class TAction, Action> const action = "action";
    auto const action_def = ('(' >> lit(":action"))
                               > name
                               > parameters
                               >> -precondition
                               >> -(lit(":effect") >> effect)
                               > ')';
    BOOST_SPIRIT_DEFINE(action);
    struct TAction: x3::annotate_on_success {};

    // Domain definition
    rule<class TDomain, Domain> const domain = "domain";
    auto const domain_def = ('(' >> lit("define")) > '('
                               >> lit("domain")
                               > name > ')'
                               > requirements
                               >> -types
                               >> -constants
                               >> -predicates
                               >> *abstract_task
                               >> *method
                               >> *action
                               > ')';
    BOOST_SPIRIT_DEFINE(domain);
    struct TDomain : x3::annotate_on_success, ErrorHandlerBase {};


    // Problem definition
    rule<class TObjects, TypedList<Name>> const objects = "objects";
    auto const objects_def = ('(' >> lit(":objects"))
                               > typed_list_names
                               > ')';
    BOOST_SPIRIT_DEFINE(objects);
    struct TObjects: x3::annotate_on_success {};

    rule<class TInit, Literal<Term>> const init = "init";
    auto const init_def = ('(' >> lit(":init"))
                               > literal_terms
                               > ')';
    BOOST_SPIRIT_DEFINE(init);
    struct TInit: x3::annotate_on_success {};

    rule<class TGoal, Sentence> const goal = "goal";
    auto const goal_def = ('(' >> lit(":goal"))
                               > sentence
                               > ')';
    BOOST_SPIRIT_DEFINE(goal);
    struct TGoal: x3::annotate_on_success {};

    rule<class TProblem, Problem> const problem = "problem";
    auto const problem_def = ('(' >> lit("define"))
                               > ('(' >> lit("problem")) > name > ')'
                               > ('(' >> lit(":domain")) > name > ')'
                               >> -requirements
                               >> -objects
                               > init
                               > goal
                               > ')';
    BOOST_SPIRIT_DEFINE(problem);
    struct TProblem: x3::annotate_on_success {};


} // namespace parser

parser::type_type type() { return parser::type; }
parser::literal_terms_type literal_terms() { return parser::literal_terms; }
parser::sentence_type sentence() { return parser::sentence; }
parser::domain_type domain() { return parser::domain; }
parser::problem_type problem() { return parser::problem; }
