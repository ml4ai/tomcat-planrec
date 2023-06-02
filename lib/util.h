#pragma once

#include <boost/json.hpp>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <iterator>
#include <random>
#include <string>
#include <variant>
#include <vector>
#include <algorithm>
#include "parsing/ast.hpp"
#include "file.hpp"

namespace json = boost::json;

json::value
parse_file( char const* filename )
{
    file f( filename, "r" );
    json::stream_parser p;
    json::error_code ec;
    do
    {
        char buf[4096];
        auto const nread = f.read( buf, sizeof(buf) );
        p.write( buf, nread, ec );
    }
    while( ! f.eof() );
    if( ec )
        return nullptr;
    p.finish( ec );
    if( ec )
        return nullptr;
    return p.release();
}

// Utility method to see if an element is in an associative container
template <class Element, class AssociativeContainer>
bool in(Element element, AssociativeContainer container) {
    return container.count(element);
}

// Utility method to see if an element is in a vector
template <class Element> bool in(Element element, std::vector<Element> v) {
    return std::find(v.begin(), v.end(), element) != v.end();
}

// Utility method to merge two vectors (duplicates allowed)
template <class Element> std::vector<Element> merge_vec(std::vector<Element> v1, std::vector<Element> v2) {
  std::vector<Element> v1v2;
  v1v2.reserve(v1.size() + v2.size());
  v1v2.insert(v1v2.end(),v1.begin(),v1.end());
  v1v2.insert(v1v2.end(),v2.begin(),v2.end());
  return v1v2;
}

// select_randomly taken from
// https://stackoverflow.com/questions/6942273/how-to-get-a-random-element-from-a-c-container
template <typename Iter, typename RandomGenerator>
Iter select_randomly(Iter start, Iter end, RandomGenerator& g) {
    std::uniform_int_distribution<> dis(0, std::distance(start, end) - 1);
    std::advance(start, dis(g));
    return start;
}

template <typename Iter> Iter select_randomly(Iter start, Iter end, int seed) {
    static std::mt19937_64 gen(seed);
    return select_randomly(start, end, gen);
}

template <typename Iter> Iter select_randomly(Iter start, Iter end) {
    static std::random_device rd;
    static std::mt19937_64 gen(rd());
    return select_randomly(start, end, gen);
}

// Helpers for std::visit
template <class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template <class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

// Support for printing variants
template <typename T, typename... Ts>
std::ostream& operator<<(std::ostream& os, const std::variant<T, Ts...>& v) {
    std::visit([&os](auto&& arg) { os << arg; }, v);
    return os;
}

void write_csv(std::string filename, std::vector<std::pair<std::string, std::vector<double>>> dataset){
    // Make a CSV file with one or more columns of integer values
    // Each column of data is represented by the pair <column name, column data>
    //   as std::pair<std::string, std::vector<int>>
    // The dataset is represented as a vector of these columns
    // Note that all columns should be the same size

    // Create an output filestream object
    std::ofstream myFile(filename);

    // Send column names to the stream
    for(int j = 0; j < dataset.size(); ++j)
    {
        myFile << dataset.at(j).first;
        if(j != dataset.size() - 1) myFile << ","; // No comma at end of line
    }
    myFile << "\n";

    // Send data to the stream
    for(int i = 0; i < dataset.at(0).second.size(); ++i)
    {
        for(int j = 0; j < dataset.size(); ++j)
        {
            myFile << dataset.at(j).second.at(i);
            if(j != dataset.size() - 1) myFile << ","; // No comma at end of line
        }
        myFile << "\n";
    }

    // Close the file
    myFile.close();
}

// Define support for printing vectors
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
    os << "(";
    for (int i = 0; i < v.size(); i++) {
        os << v.at(i);
        if (i < v.size() - 1) {
            os << " ";
        }
    }
    os << ')';
    return os;
}

const std::string WHITESPACE = " \n\r\t\f\v";
 
std::string ltrim(const std::string &s)
{
    size_t start = s.find_first_not_of(WHITESPACE);
    return (start == std::string::npos) ? "" : s.substr(start);
}
 
std::string rtrim(const std::string &s)
{
    size_t end = s.find_last_not_of(WHITESPACE);
    return (end == std::string::npos) ? "" : s.substr(0, end + 1);
}
 
std::string trim(const std::string &s) {
    return rtrim(ltrim(s));
}

struct constraints_type : public boost::static_visitor<int> {
  int operator()(const ast::Nil& n) const { return 0; }
  int operator()(const ast::Constraint& c) const { return 1; }
  int operator()(const std::vector<ast::Constraint>& vc) const { return 2; }

};

int which_constraints(ast::Constraints c) {
  return boost::apply_visitor(constraints_type(),c);
}

struct constraint_type : public boost::static_visitor<int> {
  int operator()(const ast::Nil& n) const { return 0; }
  int operator()(const ast::EqualsSentence& es) const { return 1; }
  int operator()(const ast::NotEqualsSentence& nes) const { return 2; }

};

int which_constraint(ast::Constraint c) {
  return boost::apply_visitor(constraint_type(),c);
}

struct subtasks_type : public boost::static_visitor<int> {
  int operator()(const ast::Nil& n) const { return 0; }
  int operator()(const ast::SubTask& st) const { return 1; }
  int operator()(const std::vector<ast::SubTask>& vst) const { return 2; }

};

int which_subtasks(ast::SubTasks s) {
  return boost::apply_visitor(subtasks_type(),s);
}

struct subtask_type : public boost::static_visitor<int> {
  int operator()(const ast::MTask& m) const { return 0; }
  int operator()(const ast::SubTaskWithId& stwid) const { return 1; }

};

int which_subtask(ast::SubTask s) {
  return boost::apply_visitor(subtask_type(),s);
}

struct orderings_type : public boost::static_visitor<int> {
  int operator()(const ast::Nil& n) const { return 0; }
  int operator()(const ast::Ordering& o) const { return 1; }
  int operator()(const std::vector<ast::Ordering>& ov) const { return 2; }

};

int which_orderings(ast::Orderings os) {
  return boost::apply_visitor(orderings_type(),os);
}

template <typename T> constexpr auto type_name() noexcept {
    std::string_view name = "Error: unsupported compiler", prefix, suffix;
#ifdef __clang__
    name = __PRETTY_FUNCTION__;
    prefix = "auto type_name() [T = ";
    suffix = "]";
#elif defined(__GNUC__)
    name = __PRETTY_FUNCTION__;
    prefix = "constexpr auto type_name() [with T = ";
    suffix = "]";
#elif defined(_MSC_VER)
    name = __FUNCSIG__;
    prefix = "auto __cdecl type_name<";
    suffix = ">(void) noexcept";
#endif
    name.remove_prefix(prefix.size());
    name.remove_suffix(suffix.size());
    return name;
}
