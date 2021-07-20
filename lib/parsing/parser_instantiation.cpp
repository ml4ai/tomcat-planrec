#include "config.hpp"
#include "parser_definitions.hpp"

namespace parser {
    BOOST_SPIRIT_INSTANTIATE(type_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(literal_terms_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(sentence_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(domain_type, iterator_type, context_type);
    BOOST_SPIRIT_INSTANTIATE(problem_type, iterator_type, context_type);
} // namespace parser
