#pragma once

#include "parsing/ast.hpp"
#include "util.h"
#include "z3++.h"
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

using namespace fol;

struct Type {
  std::string type;
  std::vector<int> lineage;
  std::vector<int> descendents;
};

struct TypeTree {
  std::unordered_map<int,Type> types;
  int nextID = 0;
  std::vector<int> freedIDs;
  int add_type(Type& type) {
    int id;
    if (!freedIDs.empty()) {
      id = freedIDs.back();
      freedIDs.pop_back();
    }
    else {
      id = nextID;
      nextID++;
    }
  }
  types[id] = type;
  return id;

  int find_type(std::string type) {
    for (auto const &[i,t] : this->types) {
      if (t.type == type) {
        return i;
      }  
    }
    std::string msg = "Type ";
    msg += type;
    msg += " not found!";
    throw std::logic_error(msg);
  }
};

struct KnowledgeBase {
    TypeTree typetree;
    int root; 
    // predicate: predicate data_type1 data_type2
    std::unordered_map<std::string, std::unordered_map<std::string,std::string>> predicates;
    // The true facts updating from the message bus
    std::set<std::string> pfacts;
    std::set<std::string> nfacts;

    KnowledgeBase() {
      Type type;
      type.type = "Object";
      this->root = this->typetree.add_type(type);
    }

    void add_type(std::string type, std::string ancestor) {
      Type new_t;
      new_t.type = type;
      int a = this->typetree.find_type(ancestor); 
      new_t.lineage.push_back(a);
      for (auto i : this->typetree.types[a].lineage) {
        new_t.lineage.push_back(i);
      }
      int t = this->typetree.add_type(new_t);
      this->typetree.types[a].descendents.push_back(t);
    }
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

void clear_fov_facts(KnowledgeBase &kb,
                     const std::string &predicate_name, const std::string& role);

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
