// see line 7 if problem doesn't work
#include "config.hpp"
#include "domain_def.hpp"

namespace client {
    namespace parser {
        BOOST_SPIRIT_INSTANTIATE(domain_type, iterator_type, context_type);
        BOOST_SPIRIT_INSTANTIATE(problem_type, iterator_type, context_type);
    }
} // namespace client
