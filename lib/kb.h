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
//Type struct
struct Type {
  //Name of type
  std::string type;
  //Indexes of the types lineage. 
  std::vector<int> lineage;
  //Indexes of the types children
  std::vector<int> children;
};

struct TypeTree {
  //Unordered map of the form {index,Type struct}
  std::unordered_map<int,Type> types;
  //Keeps track of next newly usable ID
  int nextID = 0;
  //Keeps track of usable freed IDs
  std::vector<int> freedIDs;
  //Adds type to TypeTree and returns its index. 
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
  //Returns index of Type struct with name type
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

//Add objects from the problem definition, then ungrounded predicate
//statements, and then run initialize before using the kb!
class KnowledgeBase {
    private:
      //Tracks type hierarchy
      TypeTree typetree;
      //Tree index for root node.
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

      //Gets all bindings for smt_statement and set of variables
      //A set of bindings is an unordered map of form {variable,value}.
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

      //Used by tell to update the smt_state string.
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
      //Constructor initializes the default type __Object__ and adds an object
      //predicate for it. 
      KnowledgeBase() {
        Type type;
        type.type = "__Object__";
        this->root = this->typetree.add_type(type);
        this->add_predicate("__Object__",{{"?o","__Object__"}});
      }
      //Takes the predicate head (e.g., At). Parameters are given as a
      //unordered map of {variable, type} (e.g., {?x, location})  
      void add_predicate(std::string head,std::unordered_map<std::string,std::string> params) {
        this->predicates[head] = params;
      }

      //Can add many predicates as once in the form of
      //{head,{variable1,type1},...}. 
      void add_predicates(std::unordered_map<std::string,std::unordered_map<std::string,std::string>> preds) {
        this->predicates.merge(preds); 
      }
      
      //Arguments are name of the object and type (e.g., Room1 - location).
      void add_object(std::string name, std::string type) {
        this->objects[name] = type;
      }
      //Types by default inherit type __Object__. If a ancestor type is
      //specified, the type will inherit that ancestor and the lineage of that
      //ancestor (including __Object__). Automatically adds object predicates.
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

   
      // Warning: This clears the KB! Initializes the KBs belief state with
      // closed world assumption.  
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

      //Returns false if contradiction is detected. Only give it a single grounded
      //predicate. Additions have remove = false, deletions are given by
      //setting remove to true. Do not give it a (not (pred)), the not will be
      //handled by the parser!
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
      //compatible prior to this call. Only grounded statements are allowed
      //here!
      bool ask(std::string expr) {
        z3::context con;
        z3::solver s(con);
        std::string smt_expr = this->smt_state+"(assert "+expr+")\n";
        s.from_string(smt_expr.c_str());
        return s.check() == z3::sat;
      }

      //This adds the assert to expr, but the rest of expr must be made smt
      //compatible prior to this call. Z3 will give an error if a variable is not
      //found in params is used, which complies with HDDLs specifications for method and
      //action definitions.  
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

      //prints all facts
      void print_pfacts() {
        for (auto const& p : this->pfacts) {
          std::cout << p << std::endl;
        }
      }
      //prints all negative facts (things that are not true).
      void print_nfacts() {
        for (auto const& n : this->nfacts) {
          std::cout << n << std::endl;
        }
      }
      //prints smt_state string
      void print_smt_state() {
        std::cout << this->smt_state << std::endl;
      }

};


