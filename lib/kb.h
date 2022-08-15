#pragma once

#include "parsing/ast.hpp"
#include "util.h"
#include "z3++.h"
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>
#include <unordered_map>

using namespace fol;

struct Type {
  std::string type;
  std::vector<int> lineage;
  std::vector<int> children;
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
    types[id] = type;
    return id;
  }

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

class KnowledgeBase {
    private:
      TypeTree typetree;
      int root; 
      //header,{{var1,type1},{var2,type2},...}
      std::unordered_map<std::string, std::unordered_map<std::string,std::string>> predicates;
      //constant, type
      std::unordered_map<std::string, std::string> objects;
      //(pred arg1 arg2 ...)
      std::set<std::string> pfacts;
      //(pred arg1 arg2 ...)
      std::set<std::string> nfacts;
      //belief state in smt form;
      std::string smt_state;

      std::vector<std::unordered_map<std::string,std::string>> 
      get_bindings(std::string F, 
                  const std::unordered_map<std::string,std::string>& variables) {
        std::vector<std::unordered_map<std::string,std::string>> results;
        z3::context con;
        z3::solver s(con);
        s.from_string(F.c_str());
        while (s.check() == z3::sat) {
          auto m = s.get_model();
          std::unordered_map<std::string,std::string> bindings;
          for (unsigned i = 0; i < m.size(); i++) {
            auto v = m[i];
            auto v_name = v.name().str();
            if(variables.find(v_name) != variables.end()) {
              bindings[v_name] = m.get_const_interp(v).to_string();
            }
          }
          results.push_back(bindings);
          z3::expr_vector block(con);
          for (unsigned j = 0; j < m.size(); j++) {
            auto d = m[j];
            if (d.arity() > 0) {
              continue;
            } 
            auto c = d();
            if (c.is_array() || c.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT) {
              throw std::logic_error("arrays and uninterpreted sorts are not supported");
            }
            block.push_back(c != m.get_const_interp(d));
          }
          s.add(z3::mk_or(block));
        }
        return results;
      }

      void update_state() {
        this->smt_state = "(declare-datatype __Object__ (";
        for (auto const& [o1,o2] : this->objects) {
          this->smt_state += o1+" ";
        }
        this->smt_state += "))\n";
        for (auto const& [h,a] : this->predicates){
          this->smt_state += "(declare-fun "+h+" (";
          for (auto const& [v,t] : a) {
            this->smt_state += "__Object__ ";
          }
          this->smt_state += ") Bool)\n";
        }
        this->smt_state += "(assert (and ";
        for (auto const& p : this->pfacts) {
          this->smt_state += p+" ";
        }

        for (auto const& n : this->nfacts) {
          this->smt_state += "(not "+n+") ";
        }
        this->smt_state += "))\n";
      }

    public:
      KnowledgeBase() {
        Type type;
        type.type = "__Object__";
        this->root = this->typetree.add_type(type);
        this->add_predicate("__Object__",{{"?o","__Object__"}});
      }

      void add_predicate(std::string head,std::unordered_map<std::string,std::string> params) {
        this->predicates[head] = params;
      }

      void add_predicates(std::unordered_map<std::string,std::unordered_map<std::string,std::string>> preds) {
        this->predicates.merge(preds); 
      }

      void add_object(std::string name, std::string type) {
        this->objects[name] = type;
      }

      void add_type(std::string type, std::string ancestor = "__Object__") {
        Type new_t;
        new_t.type = type;
        this->add_predicate(type,{{"?o","__Object__"}});
        int a = this->typetree.find_type(ancestor); 
        new_t.lineage.push_back(a);
        if (ancestor != "__Object__") {
          for (auto i : this->typetree.types[a].lineage) {
            new_t.lineage.push_back(i);
          }
        }
        int t = this->typetree.add_type(new_t);
        this->typetree.types[a].children.push_back(t);
      }

   
      // Warning: This clears the KB! 
      void initialize() {
        this->nfacts.clear();
        this->pfacts.clear();

        std::string st = "(declare-datatype __Object__ (";
        for (auto const& [o1,o2] : this->objects) {
          st += o1+" ";
          int t = this->typetree.find_type(o2);
          for (auto const& [t1,t2] : this->typetree.types) {
            std::string f = "("+t2.type+" "+o1+")";
            if (in(t1,this->typetree.types[t].lineage) ||
                t2.type == o2) {
              this->pfacts.insert(f);
            } 
            else {
              this->nfacts.insert(f);
            }
          }
        }
        st += "))\n";
        for (auto const& [h,a] : this->predicates){
          std::string pt = "(declare-fun "+h+" (";
          std::string at = "(assert ("+h+" ";
          std::string ot = "";
          for (auto const& [v,t] : a) {
            pt += "__Object__ ";
            at += v+" ";
            ot += "(declare-const "+v+" __Object__)\n";
          }
          pt += ") Bool)\n";
          at += "))\n";
          std::string smt = st + ot + pt + at;
          auto bindings = get_bindings(smt,a);
          for (auto const& binding : bindings) {
            std::string pred = "("+h+" ";
            for (auto const& [v,t] : binding) {
              pred += t+" ";
            }
            pred = trim(pred);
            pred += ")";
            if (this->pfacts.find(pred) == pfacts.end()) {
              this->nfacts.insert(pred);
            }
          }
        }
        this->update_state();
      }

      //Returns false if contradiction
      bool tell(std::string pred, bool remove = false) {
        if (remove) {
          if (this->pfacts.find(pred) != this->pfacts.end()) {
            if (this->nfacts.find(pred) != this->nfacts.end()) {
              return false;
            }
            this->pfacts.erase(pred);
            this->nfacts.insert(pred);
            this->update_state();
            return true;
          }
          if (this->nfacts.insert(pred).second) {
            this->update_state();
          }
          return true;
        }
        if (this->nfacts.find(pred) != this->nfacts.end()) {
          if (this->pfacts.find(pred) != this->pfacts.end()) {
            return false;
          }
          this->nfacts.erase(pred);
          this->pfacts.insert(pred);
          this->update_state();
          return true;
        }
        if (this->pfacts.insert(pred).second) {
          this->update_state();
        }
        return true;
      }

      //This adds the assert to expr, but the rest of expr must be made smt
      //compatible prior to this call
      bool ask(std::string expr) {
        z3::context con;
        z3::solver s(con);
        std::string smt_expr = this->smt_state+"(assert "+expr+")\n";
        s.from_string(smt_expr.c_str());
        return s.check() == z3::sat;
      }

      //This adds the assert to expr, but the rest of expr must be made smt
      //compatible prior to this call
      std::vector<std::unordered_map<std::string,std::string>>
      ask(std::string expr,
          std::unordered_map<std::string,std::string> params) {
        std::string smt_expr = this->smt_state;
        for (auto const& [v,t] : params) {
          smt_expr += "(declare-const "+v+" __Object__)\n";
          smt_expr += "(assert ("+t+" "+v+"))\n";
        }
        smt_expr += "(assert "+expr+")\n";
        return get_bindings(smt_expr,params);
      }


      void print_pfacts() {
        for (auto const& p : this->pfacts) {
          std::cout << p << std::endl;
        }
      }

      void print_nfacts() {
        for (auto const& n : this->nfacts) {
          std::cout << n << std::endl;
        }
      }

      void print_smt_state() {
        std::cout << this->smt_state << std::endl;
      }

};


