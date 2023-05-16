#pragma once

#include "Redis_Connect.h"
#include "parsing/ast.hpp"
#include "util.h"
#include "z3++.h"
#include <map>
#include <unordered_set>
#include <string>
#include <tuple>
#include <vector>
#include <unordered_map>
#include <chrono>

//Type struct
struct Type {
  //Name of type
  std::string type;
  //Indexes of the types lineage. 
  std::unordered_set<int> lineage;
  //Indexes of the types children
  std::unordered_set<int> children;
};

//TypeTree struct. This keeps track of the type inheritence hierarchy
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
  //This clears tree and adds just the root type!
  void add_root(std::string type) {
    this->types.clear();
    this->freedIDs.clear();
    this->nextID = 0;
    Type new_t;
    new_t.type = type;
    this->add_type(new_t);
  }

  void add_child(std::string type, std::string ancestor) {
    Type new_t;
    new_t.type = type;
    int a = this->find_type(ancestor); 
    new_t.lineage.insert(a);
    for (auto i : this->types[a].lineage) {
      new_t.lineage.insert(i);
    }
    int t = this->add_type(new_t);
    this->types[a].children.insert(t);  
  }

  void add_ancestor(std::string type, std::string ancestor) {
    int a = this->find_type(ancestor);
    int i = this->find_type(type);
    for (auto &[id,t] : this->types) {
      if (t.children.contains(i)) {
        t.children.erase(i); 
        t.children.insert(a);
        this->types[a].lineage.clear();
        this->types[a].lineage.insert(id);
        for (auto l : t.lineage) {
          this->types[a].lineage.insert(l);
        }
      }
    }
    this->types[a].children.insert(i);
    this->types[i].lineage.clear();
    this->types[i].lineage.insert(a);
    for (auto l : this->types[a].lineage) {
      this->types[i].lineage.insert(l);
    }
    propogate_new_lineage(i);
  }
  //Helper function for add_ancestor
  void propogate_new_lineage(int i) {
    if (this->types[i].children.empty()) {
      return;
    }
    for (auto const& c : this->types[i].children) {
      this->types[c].lineage.clear();
      this->types[c].lineage.insert(i);
      for (auto l : this->types[i].lineage) {
        this->types[c].lineage.insert(l);
      }
      propogate_new_lineage(c);
    } 
  }

  //Returns index of Type struct with name type
  int find_type(std::string type) {
    for (auto const &[i,t] : this->types) {
      if (t.type == type) {
        return i;
      }  
    }
    return -1;
  }
};

int find_var(std::vector<std::pair<std::string, std::string>> vars, std::string var) {
  for (int i = 0; i < vars.size(); i++) {
    if (vars[i].first == var) {
      return i;
    }
  }
  return -1;
}

//Add objects from the problem definition, then ungrounded predicate
//statements, and then run initialize before using the kb!
class KnowledgeBase {
    private:
      //header,{{var1,type1},{var2,type2},...}
      std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> predicates;
      //constant, type
      std::unordered_map<std::string,std::string> objects;
      //header, (header arg1 arg2 ...), ... 
      std::unordered_map<std::string, std::unordered_set<std::string>> facts;
      //time, header, (header arg1 arg2 ...), ...
      std::map<int, std::unordered_map<std::string,std::unordered_set<std::string>>, std::greater<int>> temporal_facts;
      //belief state in smt form;
      std::string smt_state;

      //Gets all bindings for smt_statement and set of variables
      //A set of bindings is an vector of pairs of form {variable,value}. Called
      //by ask when given a collection of params.
      std::vector<std::vector<std::pair<std::string,std::string>>> 
      get_bindings(std::string F, 
                  const std::vector<std::pair<std::string, std::string>>& variables) {
        std::vector<std::vector<std::pair<std::string,std::string>>> results;
        z3::context con;
        z3::solver s(con);
        s.from_string(F.c_str());
        while (s.check() == z3::sat) {
          auto m = s.get_model();
          std::vector<std::pair<std::string, std::string>> bindings = variables;
          for (unsigned i = 0; i < m.size(); i++) {
            auto v = m[i];
            auto v_name = v.name().str();
            auto index = find_var(bindings, v_name);
            if(index != -1) {
              bindings[index].second = m.get_const_interp(v).to_string();
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
      
      //Parses (header arg1 arg2 ...) into {header,{arg1, arg2, ...}}
      std::pair<std::string, std::vector<std::string>> 
      parse_predicate(std::string pred) {
        std::vector<std::string> symbols = {};
        size_t pos = 0;
        std::string p = pred.substr(1,pred.size() - 2);
        std::string space_delimiter = " ";
        while ((pos = p.find(space_delimiter)) != std::string::npos) {
          symbols.push_back(p.substr(0, pos));
          p.erase(0, pos + space_delimiter.length());
        }
        if (!p.empty()) {
          symbols.push_back(p);
        }
        std::string predicate = symbols.at(0);
        symbols.erase(symbols.begin());
        return std::make_pair(predicate, symbols);
      }

      // Initializes the KBs belief state with
      // closed world assumption. Call ONCE after adding all of the needed types, objects, and
      // predicate or else all tell() and ask() calls will crash or fail!   
      void initialize(TypeTree typetree) {
        for (auto const& [t1, t2] : typetree.types) {
          std::vector<std::pair<std::string, std::string>> params;
          params.push_back(std::make_pair("?o","__Object__"));
          this->predicates.push_back(std::make_pair(t2.type,params));
        }
        for (auto const& [o1,o2] : this->objects) {
          int t = typetree.find_type(o2);
          for (auto const& [t1,t2] : typetree.types) {
            std::string f = "("+t2.type+" "+o1+")";
            if (in(t1,typetree.types[t].lineage) ||
                t2.type == o2) {
              this->facts[t2.type].insert(f);
            } 
          }
        }
        this->update_state();
      }

    public:
      KnowledgeBase() {}
      KnowledgeBase(std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> predicates,
                    std::unordered_map<std::string,std::string> objects,
                    TypeTree typetree) {
        this->predicates = predicates;
        this->objects = objects;
        this->initialize(typetree);
      }

      //Used by tell to update the smt_state string. tell() calls this
      //automatically by default, but it can be called manually too (see tell()
      //for default settings).
      void update_state(int time = -1) {
        this->smt_state = "(declare-datatype __Object__ (";
        for (auto const& [o1,o2] : this->objects) {
          this->smt_state += o1+" ";
        }
        this->smt_state += "))\n";
        //No temporal facts
        if (time < 0 || this->temporal_facts.empty()) {
          for (auto const& p : this->predicates) {
            if (this->facts.find(p.first) != this->facts.end()) {
              if (!this->facts[p.first].empty()) {
                this->smt_state += "(declare-fun "+p.first+" (";
                std::string pred_assert = "(assert (forall (";
                int i = 0;
                std::string var_assert = "";
                for (auto const& pars : p.second) {
                  this->smt_state += "__Object__ ";
                  pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                  var_assert += " x_"+std::to_string(i);
                  i++;
                }
                pred_assert += ") (= ("+p.first+var_assert+") (or ";
                for (auto const& f : this->facts[p.first]) {
                  auto pp = this->parse_predicate(f);
                  pred_assert += "(and ";
                  int j = 0;
                  for (auto const& vals : pp.second) {
                    pred_assert += "(= x_"+std::to_string(j)+" "+vals+") ";
                    j++;
                  }
                  pred_assert += ") ";
                }
                pred_assert += "))))\n";
                this->smt_state += ") Bool)\n";
                this->smt_state += pred_assert;
              }
              else {
                this->smt_state += "(declare-fun "+p.first+" (";
                std::string pred_assert = "(assert (forall (";
                int i = 0;
                std::string var_assert = "";
                for (auto const& vars : p.second) {
                  this->smt_state += "__Object__ ";
                  pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                  var_assert += " x_"+std::to_string(i);
                  i++;
                }
                pred_assert += ") (not ("+p.first+var_assert+"))))\n";
                this->smt_state += ") Bool)\n";
                this->smt_state += pred_assert;
              }
            }
            else {
              this->smt_state += "(declare-fun "+p.first+" (";
              std::string pred_assert = "(assert (forall (";
              int i = 0;
              std::string var_assert = "";
              for (auto const& vars : p.second) {
                this->smt_state += "__Object__ ";
                pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                var_assert += " x_"+std::to_string(i);
                i++;
              }
              pred_assert += ") (not ("+p.first+var_assert+"))))\n";
              this->smt_state += ") Bool)\n";
              this->smt_state += pred_assert;
            }
          }
        }
        else {
          std::map<int, std::unordered_map<std::string,std::unordered_set<std::string>>, std::greater<int>>::iterator itlow;
          itlow = this->temporal_facts.lower_bound(time);
          int closest_time = itlow->first;
          //No relevant temporal facts
          if (time - closest_time > 1000 || closest_time > time) {
            for (auto const& p : this->predicates) {
              if (this->facts.find(p.first) != this->facts.end()) {
                if (!this->facts[p.first].empty()) {
                  this->smt_state += "(declare-fun "+p.first+" (";
                  std::string pred_assert = "(assert (forall (";
                  int i = 0;
                  std::string var_assert = "";
                  for (auto const& pars : p.second) {
                    this->smt_state += "__Object__ ";
                    pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                    var_assert += " x_"+std::to_string(i);
                    i++;
                  }
                  pred_assert += ") (= ("+p.first+var_assert+") (or ";
                  for (auto const& f : this->facts[p.first]) {
                    auto pp = this->parse_predicate(f);
                    pred_assert += "(and ";
                    int j = 0;
                    for (auto const& vals : pp.second) {
                      pred_assert += "(= x_"+std::to_string(j)+" "+vals+") ";
                      j++;
                    }
                    pred_assert += ") ";
                  }
                  pred_assert += "))))\n";
                  this->smt_state += ") Bool)\n";
                  this->smt_state += pred_assert;
                }
                else {
                  this->smt_state += "(declare-fun "+p.first+" (";
                  std::string pred_assert = "(assert (forall (";
                  int i = 0;
                  std::string var_assert = "";
                  for (auto const& vars : p.second) {
                    this->smt_state += "__Object__ ";
                    pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                    var_assert += " x_"+std::to_string(i);
                    i++;
                  }
                  pred_assert += ") (not ("+p.first+var_assert+"))))\n";
                  this->smt_state += ") Bool)\n";
                  this->smt_state += pred_assert;
                }
              }
              else {
                this->smt_state += "(declare-fun "+p.first+" (";
                std::string pred_assert = "(assert (forall (";
                int i = 0;
                std::string var_assert = "";
                for (auto const& vars : p.second) {
                  this->smt_state += "__Object__ ";
                  pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                  var_assert += " x_"+std::to_string(i);
                  i++;
                }
                pred_assert += ") (not ("+p.first+var_assert+"))))\n";
                this->smt_state += ") Bool)\n";
                this->smt_state += pred_assert;
              }
            }
          }
          else {
            //Add temporal facts
            for (auto const& p : this->predicates) {
              bool t_facts_exist = false;
              if (this->temporal_facts[closest_time].find(p.first) != this->temporal_facts[closest_time].end()) {
                if (!this->temporal_facts[closest_time][p.first].empty()) {
                  t_facts_exist = true;
                }
              }
              if (t_facts_exist) {
                this->smt_state += "(declare-fun "+p.first+" (";
                std::string pred_assert = "(assert (forall (";
                int i = 0;
                std::string var_assert = "";
                for (auto const& pars : p.second) {
                  this->smt_state += "__Object__ ";
                  pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                  var_assert += " x_"+std::to_string(i);
                  i++;
                }
                pred_assert += ") (= ("+p.first+var_assert+") (or ";
                for (auto const& f : this->temporal_facts[closest_time][p.first]) {
                  auto pp = this->parse_predicate(f);
                  pred_assert += "(and ";
                  int j = 0;
                  for (auto const& vals : pp.second) {
                    pred_assert += "(= x_"+std::to_string(j)+" "+vals+") ";
                    j++;
                  }
                  pred_assert += ") ";
                }
                pred_assert += "))))\n";
                this->smt_state += ") Bool)\n";
                this->smt_state += pred_assert;
              }

              bool facts_exist = false;
              if (this->facts.find(p.first) != this->facts.end()) {
                if (!this->facts[p.first].empty()) {
                  facts_exist = true;
                }
              }
              if (facts_exist) {
                  this->smt_state += "(declare-fun "+p.first+" (";
                  std::string pred_assert = "(assert (forall (";
                  int i = 0;
                  std::string var_assert = "";
                  for (auto const& pars : p.second) {
                    this->smt_state += "__Object__ ";
                    pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                    var_assert += " x_"+std::to_string(i);
                    i++;
                  }
                  pred_assert += ") (= ("+p.first+var_assert+") (or ";
                  for (auto const& f : this->facts[p.first]) {
                    auto pp = this->parse_predicate(f);
                    pred_assert += "(and ";
                    int j = 0;
                    for (auto const& vals : pp.second) {
                      pred_assert += "(= x_"+std::to_string(j)+" "+vals+") ";
                      j++;
                    }
                    pred_assert += ") ";
                  }
                  pred_assert += "))))\n";
                  this->smt_state += ") Bool)\n";
                  this->smt_state += pred_assert;
              }

              if (!t_facts_exist && !facts_exist) {
                this->smt_state += "(declare-fun "+p.first+" (";
                std::string pred_assert = "(assert (forall (";
                int i = 0;
                std::string var_assert = "";
                for (auto const& vars : p.second) {
                  this->smt_state += "__Object__ ";
                  pred_assert += "(x_"+std::to_string(i)+" __Object__) ";
                  var_assert += " x_"+std::to_string(i);
                  i++;
                }
                pred_assert += ") (not ("+p.first+var_assert+"))))\n";
                this->smt_state += ") Bool)\n";
                this->smt_state += pred_assert;
              }
            }
          }
        }
      }

      //Returns false if predicate type is not found. Only give it a single grounded
      //predicate in (header arg1 arg2 ...) form. Adding facts requires that remove = false (default) and 
      //deleting facts require that remove = true. 
      //Do not give it a (not (pred)), the "not" will be
      //handled by the parser!
      //By Default, it calls update_state(). If you are calling this in a long
      //series or loop, set update_state = false and then call update_state()
      //manually after all the tells for more optimal performance! 
      bool tell(std::string pred, bool remove = false, bool update_state = true, int time = -1) {
        auto pp = this->parse_predicate(pred);
        bool not_found = true;
        for (auto const& p : this->predicates) {
          if (pp.first == p.first and pp.second.size() == p.second.size()) {
            not_found = false;
          }  
        }
        if (not_found) {
          return false;
        }
        if (time < 0) {
          if (remove) {
            this->facts[pp.first].erase(pred);
            if (update_state) { 
              this->update_state();
            }
            return true;
          }
          this->facts[pp.first].insert(pred);
          if (update_state) {
            this->update_state();
          }
          return true;
        }
        else {
          if (remove) {
            this->temporal_facts[time][pp.first].erase(pred);
            if (update_state) { 
              this->update_state(time);
            }
            return true;
          }
          this->temporal_facts[time][pp.first].insert(pred);
          if (update_state) {
            this->update_state(time);
          }
          return true;
        }
      }

      //This adds the assert to expr, but the rest of expr must be made smt
      //compatible prior to this call. Z3 will give an error if a variable is not
      //found in params is used, which complies with HDDLs specifications for method and
      //action definitions. Params must be {{var1,type1},{var2,type2},...} 
      //This returns {{{var1,val1},{var2,val2},...},...}
      //EX: expr = (and (A ?x) (or (B ?x y) (C z)))
      //params = {{"?x", "thing"}}
      std::vector<std::vector<std::pair<std::string,std::string>>>
      ask(std::string expr,
          std::vector<std::pair<std::string, std::string>>& params) {
        std::string smt_expr = this->smt_state;
        for (auto const& p : params) {
          smt_expr += "(declare-const "+p.first+" __Object__)\n";
          smt_expr += "(assert ("+p.second+" "+p.first+"))\n";
        }
        if (expr != "") {
          smt_expr += "(assert "+expr+")\n";
        }
        return get_bindings(smt_expr,params);
      }

      //This adds the assert to expr, but the rest of expr must be made smt
      //compatible prior to this call. 
      //This is mostly an issue for things like forall and exist, which have different
      //syntax in smt compared to hddl. 
      //Only grounded statements are allowed here!
      //EX: (and (A x) (or (B x y) (C z)))
      bool ask(std::string expr) {
        z3::context con;
        z3::solver s(con);
        std::string smt_expr = this->smt_state+"(assert "+expr+")\n";
        s.from_string(smt_expr.c_str());
        return s.check() == z3::sat;
      }


      //prints smt_state string
      void print_smt_state() {
        std::cout << this->smt_state << std::endl;
      }

      std::unordered_set<std::string> get_facts(std::string head) {
        return this->facts[head];
      } 

      void print_facts() {
        for (auto const& [_,fset] : this->facts) {
          for (auto const& fact : fset) {
            std::cout << fact << std::endl;
          }
        }
      }
      
      void update_temporal_facts(std::string const& redis_address) {
        Redis_Connect* rc = Redis_Connect::getInstance(redis_address); 
        std::string oldest;
        if (this->temporal_facts.empty()) {
          oldest = "0";
        }
        else {
          oldest = std::to_string(this->temporal_facts.begin()->first);
        }
        std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> xresults;
        rc->redis.xread("fov",oldest,std::back_inserter(xresults));
        for (auto const& x : xresults) {
          int t = std::stoi(x.first);
          for (auto const& y : x.second) {
            this->temporal_facts[t][y.first].insert(y.second);
          }
        }
      }

      bool temporal_facts_is_empty() {
        return this->temporal_facts.empty();
      }

      std::unordered_map<std::string, std::unordered_set<std::string>>
      get_facts() {
        return this->facts;
      }
};


