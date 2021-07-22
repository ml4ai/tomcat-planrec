#pragma once

#include <boost/variant.hpp>

template <typename T, typename... Ts>
std::ostream& operator<<(std::ostream& os, const boost::variant<T, Ts...>& v) {
    boost::apply_visitor([&os](auto&& arg) { os << arg; }, v);
    return os;
}

template <class Visitor, class T> auto visit(T x) {
    return boost::apply_visitor(Visitor(), x);
}

template <class Visitor, class T, class U> auto visit(T x, U y) {
    return boost::apply_visitor(Visitor(), x, y);
}
