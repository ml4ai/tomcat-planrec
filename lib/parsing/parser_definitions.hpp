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
    auto const requirement_def = ':' > name;
    BOOST_SPIRIT_DEFINE(requirement);

    rule<class TPredicate, Name> const predicate = "predicate";
    auto const predicate_def = name;
    BOOST_SPIRIT_DEFINE(predicate);

    rule<class TRequirements, std::vector<Name>> const requirements =
        "requirements";
    auto const requirements_def = '(' >> lit(":requirements") >> +requirement >>
                                  ')';
    BOOST_SPIRIT_DEFINE(requirements);

    rule<class TConstant, Constant> const constant = "constant";
    auto const constant_def = name;
    BOOST_SPIRIT_DEFINE(constant);

    rule<class TVariable, Variable> const variable = "variable";
    auto const variable_def = '?' > name;
    BOOST_SPIRIT_DEFINE(variable);

    rule<class TPrimitiveType, PrimitiveType> const primitive_type =
        "primitive_type";
    auto const primitive_type_def = name;
    BOOST_SPIRIT_DEFINE(primitive_type);

    rule<class TEitherType, EitherType> const either_type = "either_type";
    auto const either_type_def = '(' >> lit("either") >> +primitive_type >> ')';
    BOOST_SPIRIT_DEFINE(either_type);

    rule<class TType, Type> const type = "type";
    auto const type_def = primitive_type | either_type;
    BOOST_SPIRIT_DEFINE(type);

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
    rule<class TAtomicFormulaSkeleton, AtomicFormulaSkeleton> const
        atomic_formula_skeleton = "atomic_formula_skeleton";
    auto const atomic_formula_skeleton_def =
        '(' >> name >> typed_list_variables >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_skeleton);

    // Term
    rule<class TTerm, Term> const term = "term";
    auto const term_def = constant | variable;
    BOOST_SPIRIT_DEFINE(term);

    // Atomic formula of terms
    rule<class TAtomicFormulaTerms, AtomicFormula<Term>> const
        atomic_formula_terms = "atomic_formula_terms";
    auto const atomic_formula_terms_def = '(' >> predicate >> *term >> ')';
    BOOST_SPIRIT_DEFINE(atomic_formula_terms);

    // Literals of terms
    rule<class TLiteralTerms, Literal<Term>> const literal_terms =
                                 "literal_terms";
    auto const literal_terms_def = atomic_formula_terms;
    BOOST_SPIRIT_DEFINE(literal_terms);

    // Nil
    rule<class TNil, Nil> const nil = "nil";
    auto const nil_def = '(' >> lit(")");
    BOOST_SPIRIT_DEFINE(nil);

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


    rule<class TNotSentence, NotSentence> const not_sentence =
                                  "not_sentence";
    auto const not_sentence_def = '('
                               >> lit("not")
                               >> sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(not_sentence);


    rule<class TImplySentence, ImplySentence> const imply_sentence =
                                   "imply_sentence";
    auto const imply_sentence_def = '('
                               >> lit("imply")
                               >> sentence
                               >> sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(imply_sentence);


    rule<class TExistsSentence, ExistsSentence> const exists_sentence =
                                   "exists_sentence";
    auto const exists_sentence_def = '('
                               >> lit("exists")
                               >> '('
                               >> typed_list_variables
                               >> ')'
                               >> sentence
                               >> ')';
    BOOST_SPIRIT_DEFINE(exists_sentence);


    rule<class TForallSentence, ForallSentence> const forall_sentence =
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
    auto const types_def = '(' 
                               >> lit(":types") 
                               >> typed_list_names 
                               >> ')';
    BOOST_SPIRIT_DEFINE(types);

    rule<class TConstants, TypedList<Name>> const constants = "constants";
    auto const constants_def = '(' 
                               >> lit(":constants") 
                               >> typed_list_names 
                               >> ')';
    BOOST_SPIRIT_DEFINE(constants);

    rule<class TPredicates, std::vector<AtomicFormulaSkeleton>> const
        predicates = "predicates";
    auto const predicates_def = '(' 
                               >> lit(":predicates") 
                               >> +atomic_formula_skeleton >> ')';
    BOOST_SPIRIT_DEFINE(predicates);

    rule<class TPrecondition, Sentence> const precondition = "precondition";
    auto const precondition_def = lit(":precondition")
                               >> sentence;
    BOOST_SPIRIT_DEFINE(precondition);

    rule<class TEffect, Sentence> const effect = "effect";
    auto const effect_def = lit(":effect")
                              >> sentence;
    BOOST_SPIRIT_DEFINE(effect);

    rule<class TParameters, TypedList<Variable>> const parameters = "parameters";
    auto const parameters_def = lit(":parameters")
                               >> '('
                               >> typed_list_variables
                               >> ')';
    BOOST_SPIRIT_DEFINE(parameters);

    rule<class TTask, Task> const task = "task";
    auto const task_def = name >> parameters;
    BOOST_SPIRIT_DEFINE(task);


    // Abstract Tasks
    rule<class TAbstractTask, Task> const abstract_task = "abstract_task";
    auto const abstract_task_def = '(' >> lit(":task") >> task >> ')';
    BOOST_SPIRIT_DEFINE(abstract_task);


    rule<class TTaskSymbolWithTerms, MTask> const task_symbol_with_terms = "task_symbol_with_terms";
    auto const task_symbol_with_terms_def = '(' >> name >> *term >> ')';
    BOOST_SPIRIT_DEFINE(task_symbol_with_terms);

    // Methods used to decompose abstract tasks into primitive actions
    // task as defined in Method struct != task defined in task struct
    // mtask refers to task definition found within a method:
    rule<class TMTask, MTask> const mtask = "mtask";
    auto const mtask_def = lit(":task") >> task_symbol_with_terms;
    BOOST_SPIRIT_DEFINE(mtask);

    rule<class TSubTaskWithId, SubTaskWithId> const subtask_with_id = "subtask_with_id";
    auto const subtask_with_id_def = '(' >> name >> task_symbol_with_terms >> ')';
    BOOST_SPIRIT_DEFINE(subtask_with_id);

    rule<class TSubTask, SubTask> const subtask = "subtask";
    auto const subtask_def = task_symbol_with_terms | subtask_with_id;
    BOOST_SPIRIT_DEFINE(subtask);

    rule<class TSubTasks, SubTasks> const subtasks = "subtasks";
    auto const subtasks_def = nil | subtask | '(' >> lit("and") >> +subtask >> ')';
    BOOST_SPIRIT_DEFINE(subtasks);

    rule<class TOrdering, Ordering> const ordering = "ordering";
    auto const ordering_def = '(' >> name >> '<' >> name >> ')';
    BOOST_SPIRIT_DEFINE(ordering);

    rule<class TOrderings, Orderings> const orderings = "orderings";
    auto const orderings_def = nil | ordering | '(' >> lit("and") >> +ordering >> ')';
    BOOST_SPIRIT_DEFINE(orderings);

    rule<class TTaskNetworkOrderings, Orderings> const task_network_orderings = "task_network_orderings";
    auto const task_network_orderings_def = lit(":ordering") >> orderings;
    BOOST_SPIRIT_DEFINE(task_network_orderings);

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
    auto const method_subtasks_def = ':' > ordering_kw >> subtasks;
    BOOST_SPIRIT_DEFINE(method_subtasks);

    rule<class TConstraint, Sentence> const constraint = "constraint";
    auto const constraint_def = lit(":constraints")
                               >> sentence;
         // Will not parse '=' constraints right now. Come back
    BOOST_SPIRIT_DEFINE(constraint);

    rule<class TTaskNetwork, TaskNetwork> const task_network = "task_network";
    auto const task_network_def = method_subtasks >> task_network_orderings;
    BOOST_SPIRIT_DEFINE(task_network);



    rule<class TMethod, Method> const method = "method";
    auto const method_def = '(' >> lit(":method")
                                >> name
                                >> parameters
                                >> mtask // one task
                                >> precondition
                                >> task_network
                                >> ')';
    BOOST_SPIRIT_DEFINE(method);


    // Primitive actions
    rule<class TAction, Action> const action = "action";
    auto const action_def = '('
                               >> lit(":action")
                               >> name
                               >> parameters 
                               >> -precondition
                               >> -effect
                               >> ')';
    BOOST_SPIRIT_DEFINE(action);

    // Domain definition
    rule<class TDomain, Domain> const domain = "domain";
    auto const domain_def = '(' >> lit("define") >> '('
                               >> lit("domain")
                               >> name >> ')'
                               >> requirements
                               >> -types
                               >> -constants
                               >> -predicates 
                               >> *abstract_task
                               >> *method
                               >> *action
                               >> ')';
    BOOST_SPIRIT_DEFINE(domain);


    // Problem definition
    rule<class TObjects, TypedList<Name>> const objects = "objects";
    auto const objects_def = '(' >> lit(":objects") 
                               >> typed_list_names 
                               >> ')';
    BOOST_SPIRIT_DEFINE(objects);

    rule<class TInit, Literal<Term>> const init = "init";
    auto const init_def = '(' >> lit(":init") 
                               >> literal_terms 
                               >> ')';
    BOOST_SPIRIT_DEFINE(init);

    rule<class TGoal, Sentence> const goal = "goal";
    auto const goal_def = '(' >> lit(":goal") 
                               >> sentence 
                               >> ')';
    BOOST_SPIRIT_DEFINE(goal);

    rule<class TProblem, Problem> const problem = "problem";
    auto const problem_def = '(' >> lit("define")
                               >> '(' >> lit("problem") >> name >> ')'
                               >> '(' >> lit(":domain") >> name >> ')'
                               >> -requirements
                               >> -objects
                               >> init
                               >> goal
                               >> ')';
    BOOST_SPIRIT_DEFINE(problem);


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
