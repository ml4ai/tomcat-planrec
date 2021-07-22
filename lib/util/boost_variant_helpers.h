#pragma once

#include <boost/variant.hpp>

template <class Visitor, class T> auto visit(T x) {
    return boost::apply_visitor(Visitor(), x);
}

template <class Visitor, class T, class U> auto visit(T x, U y) {
    return boost::apply_visitor(Visitor(), x, y);
}
