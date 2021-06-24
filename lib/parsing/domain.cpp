#include "config.hpp"
#include "domain_def.hpp"

namespace parser {
    BOOST_SPIRIT_INSTANTIATE(constant_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(variable_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(primitive_type_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(either_type_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(type_type, iterator_type, context_type);

    // Typed list of names
    BOOST_SPIRIT_INSTANTIATE(implicitly_typed_list_names_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(explicitly_typed_list_names_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(typed_list_names_type, iterator_type, context_type);

    BOOST_SPIRIT_INSTANTIATE(atomic_formula_skeleton_type, iterator_type, context_type);

    BOOST_SPIRIT_INSTANTIATE(atomic_formula_terms_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(sentence_type, iterator_type, context_type);

    BOOST_SPIRIT_INSTANTIATE(domain_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(problem_type, iterator_type, context_type);
} // namespace parser
