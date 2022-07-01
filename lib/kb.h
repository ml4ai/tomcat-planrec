#pragma once

#include "parsing/ast.hpp"
#include "util.h"
#include "z3++.h"
#include <map>
#include <string>
#include <tuple>
#include <vector>

using namespace fol;

struct KnowledgeBase {
    // data_type: {candidate1, candidate2, ...}
    std::map<std::string, std::vector<std::string>> data_types;
    // symbol: data_type
    std::map<std::string, std::string> symbols;
    // predicate: predicate data_type1 data_type2
    std::map<std::string, std::vector<std::string>> predicates;
    // The true facts updating from the message bus
    std::map<std::string, std::set<std::vector<std::string>>> facts;
    // The operations defined by the HDDL domain representation
    std::set<std::string> domain_context;
};

void initialize_data_type(KnowledgeBase& kb,
                          const std::string& data_type_name,
                          std::vector<std::string> data_type_candidates);

void initialize_symbol(KnowledgeBase& kb,
                       const std::string& symbol_name,
                       std::string symbol_type);

void initialize_predicate(KnowledgeBase& kb,
                          const std::string& predicate_name,
                          std::vector<std::string> predicate_var_types);

std::tuple<std::string, std::vector<std::string>> parse_predicate(std::string pred);

std::string get_smt(KnowledgeBase& kb);

bool ask(KnowledgeBase& kb, const std::string& query);

std::map<std::string, std::vector<std::string>> ask_vars(KnowledgeBase& kb,
                                          const std::string& query);


void add_fact(KnowledgeBase& kb, const std::string& predicate);

bool is_predicate(KnowledgeBase& kb, std::string str);

void tell(KnowledgeBase& kb,
          const std::string& knowledge,
          int cw_var_idx = -1,
          bool unique = true);
