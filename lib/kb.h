#pragma once

#include "CNF.h"
#include "Clause.h"
#include "fol/Literal.h"
#include "fol/Predicate.h"
#include "fol/Term.h"
#include "parsing/ast.hpp"
#include "unification.h"
#include "util.h"
#include "z3++.h"
#include <algorithm>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <variant>
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
                          std::vector<std::string> data_type_candidates) {
    if (kb.data_types.count(data_type_name) == 0) {
        kb.data_types[data_type_name] = data_type_candidates;
    }
}

void initialize_symbol(KnowledgeBase& kb,
                       const std::string& symbol_name,
                       std::string symbol_type) {
    if (kb.symbols.count(symbol_name) == 0) {
        kb.symbols[symbol_name] = symbol_type;
    }
}

void initialize_predicate(KnowledgeBase& kb,
                          const std::string& predicate_name,
                          std::vector<std::string> predicate_var_types) {
    if (kb.predicates.count(predicate_name) == 0) {
        kb.predicates[predicate_name] = predicate_var_types;
        kb.facts[predicate_name] = {};
    }
}

std::tuple<std::string, std::vector<std::string>> parse_predicate(std::string pred) {
    std::vector<std::string> symbols{};
    size_t pos = 0;
    std::string space_delimiter = " ";
    while ((pos = pred.find(space_delimiter)) != string::npos) {
        symbols.push_back(pred.substr(0, pos));
        pred.erase(0, pos + space_delimiter.length());
    }
    if (!pred.empty()) {
        symbols.push_back(pred);
    }
    std::string predicate = symbols.at(0);
    symbols.erase(symbols.begin());
    return {predicate, symbols};
}

std::string get_smt(KnowledgeBase& kb) {
    std::string smt_string;
    std::string con;
    for (const auto& dt : kb.data_types) {
        con = "(declare-datatype ";
        con += dt.first + " (";
        for (const auto& var : dt.second) {
            con += "(" + var + ") ";
        }
        con += "))";
        smt_string += con;
        con = "";
    }

    for (const auto& sym : kb.symbols) {
        con = "(declare-fun ";
        con += sym.first + "() " + sym.second + ")";
        smt_string += con;
        con = "";
    }

    for (const auto& pred : kb.predicates) {
        con = "(declare-fun ";
        con += pred.first + " (";
        for (const auto& var : pred.second) {
            con += var + " ";
        }
        con += ") Bool)";
        smt_string += con;
        con = "";
    }

    for (const auto& f : kb.facts) {
        for (const auto& arg_set : f.second) {
            con = "(assert (" + f.first;
            for (const auto& arg : arg_set) {
                con += " " + arg;
            }
            con += "))";
            smt_string += con;
            con = "";
        }
        // add the closed world condition
        con = "(assert (forall (";
        for (int i = 0; i < kb.predicates[f.first].size(); i++) {
            con += "(cw_var_" + to_string(i) + " " + kb.predicates[f.first][i] +
                   ")";
        }
        con += ")";
        if (f.second.empty()) {
            con += "(not (" + f.first;
            for (int i = 0; i < kb.predicates[f.first].size(); i++) {
                con += " cw_var_" + to_string(i);
            }
            con += "))))";
            smt_string += con;
            con = "";
        }
        else {
            if (f.second.size() == 1) {
                con += " (=> (not";
            }
            else {
                con += " (=> (not (or";
            }
            for (const auto& arg_set_ : f.second) {
                con += " (and";
                for (int i = 0; i < arg_set_.size(); i++) {
                    con += " (= cw_var_" + to_string(i);
                    con += " " + arg_set_[i] + ")";
                }
                con += ")";
            }
            if (f.second.size() == 1) {
                con += ")";
            }
            else {
                con += "))";
            }

            con += " (not (" + f.first;
            for (int i = 0; i < kb.predicates[f.first].size(); i++) {
                con += " cw_var_" + to_string(i);
            }
            con += ")))))";
            smt_string += con;
            con = "";
        }
    }

    for (const auto& df : kb.domain_context) {
        con = "(assert (" + df + "))";
        smt_string += con;
        con = "";
    }

    return smt_string;
}

std::map<std::string, std::vector<std::string>> ask(KnowledgeBase& kb,
                                          const std::string& query) {
    z3::context c;
    z3::solver s(c);
    std::map<std::string, std::vector<std::string>> res;
    auto query_ = query.substr(1, query.length() - 2);
    auto smt_string = get_smt(kb);
    if (query_.find('?') != std::string::npos) {
        auto [pred, args] = parse_predicate(query_);
        auto data_type = kb.predicates[pred];
        for (int i = 0; i < args.size(); i++) {
            if (args[i].find('?') != std::string::npos) {
                // " (declare-fun r () Role)\n"
                std::string var_string =
                    "(declare-fun " + args[i] + " () " + data_type[i] + " )";
                smt_string += var_string;
            }
        }
        smt_string += "(assert (" + query_ + "))";
        // search all solutions
        s.from_string(smt_string.c_str());
        auto result = s.check();
        std::string st = "";
        while (result == z3::sat) {
            auto m = s.get_model();
            st = "";
            if (m.size() == 1) {
                z3::func_decl v = m[0];
                if (m.get_const_interp(v)) {
                    //                    std::cout << v.name() << " = " <<
                    //                    m.get_const_interp(v)
                    //                              << "\n";
                    res[v.name().str()].push_back(
                        m.get_const_interp(v).to_string());
                    st += "(assert (not (= " + v.name().str() + " " +
                          m.get_const_interp(v).to_string() + ")))";
                }
            }
            else {
                st += "(assert (not (and ";
                for (unsigned i = 0; i < m.size(); i++) {
                    z3::func_decl v = m[i];
                    if (m.get_const_interp(v)) {
                        res[v.name().str()].push_back(
                            m.get_const_interp(v).to_string());
                        st += "(= " + v.name().str() + " " +
                              m.get_const_interp(v).to_string() + ") ";
                    }
                }
                st += ")))";
            }

            smt_string += st;
            s.from_string(smt_string.c_str());
            result = s.check();
        }
    }
    else {
        smt_string += "(assert (not (" + query_ + ")))";
        s.from_string(smt_string.c_str());

        switch (s.check()) {
        case z3::unsat:
            res["assertion"] = {"sat"};
            return res;
        case z3::sat:
            res["assertion"] = {"unsat"};
            return res;
        case z3::unknown:
            res["assertion"] = {"unknown"};
            return res;
        }
    }
    return res;
}

void add_fact(KnowledgeBase& kb, const std::string& predicate) {
    auto [pred, args] = parse_predicate(predicate);
    kb.facts[pred].insert(args);
}

bool is_predicate(KnowledgeBase& kb, std::string str) {
    auto [pred, args] = parse_predicate(str);
    if (kb.predicates.count(pred) == 0) {
        return false;
    }
    else if (kb.predicates[pred].size() != args.size()) {
        return false;
    }
    return true;
}

void tell(KnowledgeBase& kb,
          const std::string& knowledge,
          int cw_var_idx = -1,
          bool unique = true) {
    auto knowledge_ = knowledge.substr(1, knowledge.length() - 2);
    // check if it exists in kb
    auto res = ask(kb, knowledge);
    if (res["assertion"].at(0) == "sat") {
        return;
    }
    else {
        if (!is_predicate(kb, knowledge_)) {
            kb.domain_context.insert(knowledge);
        }
        else {
            if (unique) {
                auto [pred, args] = parse_predicate(knowledge_);
                if (cw_var_idx == -1) {
                    cw_var_idx = args.size() - 1;
                }
                auto query = "(" + pred;
                for (int i = 0; i < args.size(); i++) {
                    if (i != cw_var_idx) {
                        query += " " + args[i];
                    }
                    else {
                        query += " ?var";
                    }
                }
                query += ")";
                auto res_ = ask(kb, query);
                if (res_.empty()) {
                    add_fact(kb, knowledge_);
                }
                else {
                    for (const auto& r : res_["?var"]) {
                        std::vector<std::string> removed_set{};
                        for (int i = 0; i < args.size(); i++) {
                            if (i != cw_var_idx) {
                                removed_set.push_back(args[i]);
                            }
                            else {
                                removed_set.push_back(r);
                            }
                        }
                        kb.facts[pred].erase(removed_set);
                    }
                    kb.facts[pred].insert(args);
                }
            }
            else {
                add_fact(kb, knowledge_);
            }
        }
    }
}
