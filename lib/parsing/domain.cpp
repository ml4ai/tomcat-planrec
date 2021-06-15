#include "config.hpp"
#include "domain_def.hpp"

namespace client {
    namespace parser {
        BOOST_SPIRIT_INSTANTIATE(domain_type, iterator_type, context_type);
    }
} // namespace client
