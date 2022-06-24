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
// using namespace z3;
// using namespace ast;
using namespace std;
using namespace fol;

// base data structs of the knowledge base to be populated using tell()
struct KnowledgeBase {
    // date_type: {candidate1, candidate2, ...}
    map<std::string, vector<std::string>> data_types;
    // symbol: data_type
    map<std::string, std::string> symbols;
    // predicate: predicate data_type1 data_type2
    map<std::string, vector<std::string>> predicates;
    // The true facts updating from the message bus
    map<std::string, vector<vector<std::string>>> facts;
    // The operations defined by the HDDL domain representation
    vector<std::string> domain_context;
};

void initialize_data_type(KnowledgeBase& kb,
                          const std::string& data_type_name,
                          vector<std::string> data_type_candidates) {
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
                          vector<std::string> predicate_var_types) {
    if (kb.predicates.count(predicate_name) == 0) {
        kb.predicates[predicate_name] = predicate_var_types;
        kb.facts[predicate_name] = {};
    }
}

std::tuple<std::string, vector<std::string>> parse_predicate(std::string pred) {
    vector<std::string> symbols{};
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
            con += ")))))";
            smt_string += con;
            con = "";
        }
        else {
            con += "(=> (not (or (and";
            for (const auto& arg_set_ : f.second) {
                for (int i = 0; i < arg_set_.size(); i++) {
                    con += " (= cw_var_" + to_string(i);
                    con += arg_set_[i] + ")";
                }
            }
            con += ")";
            con += "(not (" + f.first;
            for (int i = 0; i < kb.predicates[f.first].size(); i++) {
                con += " cw_var_" + to_string(i);
            }
            con += ")))))))";
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

map<std::string, vector<std::string>> ask(KnowledgeBase& kb,
                                          const std::string& query) {
    z3::context c;
    z3::solver s(c);
    map<std::string, vector<std::string>> res;
    auto query_ = query.substr(1, query.length() - 2);
    auto smt_string = get_smt(kb);
    if (query_.find('?') != std::string::npos) {
        auto [pred, args] = parse_predicate(query_);
        auto date_type = kb.predicates[pred];
        for (int i = 0; i < args.size(); i++) {
            if (args[i].find('?') != std::string::npos) {
                // " (declare-fun r () Role)\n"
                std::string var_string =
                    "(declare-fun " + args[i] + " () " + date_type[i] + " )";
                smt_string += var_string;
            }
        }
        smt_string += "(assert (" + query_ + "))";
        // search all solutions
        s.from_string(smt_string.c_str());
        auto result = s.check();

        //    model m = s.get_model();
        std::string st = "";
        while (result == z3::sat) {
            auto m = s.get_model();
            st = "";
            if (m.size() == 1) {
                z3::func_decl v = m[0];
                // this problem contains only constants
                if (m.get_const_interp(v)) {
                    std::cout << v.name() << " = " << m.get_const_interp(v)
                              << "\n";
                    res[v.name().str()].push_back(
                        m.get_const_interp(v).to_string());
                    st += "(assert (not (= " + v.name().str() + " " +
                          m.get_const_interp(v).to_string() + ")))";
                }
            }
            else {
                // (assert (not (and () () () )))
                st += "(assert (not (and ";
                for (unsigned i = 0; i < m.size(); i++) {
                    z3::func_decl v = m[i];
                    // this problem contains only constants
                    if (m.get_const_interp(v)) {
                        //                        std::cout << v.name() << " = "
                        //                        << m.get_const_interp(v)
                        //                                  << "\n";
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

void add_predicate(KnowledgeBase& kb,
                   const std::string& predicate,
                   const vector<int>& cw_key = {0}) {
    kb.context.push_back(predicate);

    // add the closed world sentence
    if (!cw_key.empty()) {
        auto [pred, args] = parse_predicate(predicate);

        std::string cw_sen;
        std::string new_pred;
        int var_counter = 0;
        for (int i = 0; i < args.size(); i++) {
            auto date_types = kb.predicates[pred];
            if (std::find(cw_key.begin(), cw_key.end(), i) == cw_key.end()) {
                cw_sen = "forall ((cw_var_" + to_string(var_counter) + " " +
                         date_types[i] + ")) (=> (not (= cw_var_" +
                         to_string(var_counter) + " " + args[i] + ")) (not (";
                new_pred = "";
                if (!args.empty()) {
                    new_pred += pred + " ";
                }
                for (int j = 0; j < args.size(); j++) {
                    if (i != j) {
                        new_pred += args[j] + " ";
                    }
                    else {
                        new_pred += "cw_var_" + to_string(var_counter) + " ";
                    }
                }
                cw_sen += new_pred + ")))";
                kb.context.push_back(cw_sen);
                var_counter++;
            }
        }
    }
}

void tell(KnowledgeBase& kb, const std::string& lit, int cw_var_idx = -1) {
    auto lit_ = lit.substr(1, lit.length() - 2);
    if (kb.context.empty()) {
        add_predicate(kb, lit_);
        return;
    }
    // check if exists in kb
    auto res = ask(kb, lit);
    if (res["assertion"].at(0) == "sat") {
        return;
    }
    else {
        auto [pred, args] = parse_predicate(lit_);
        auto query = "(" + pred;
        for (int i = 0; i < args.size(); i++) {
            if (find(cw_key.begin(), cw_key.end(), i) == cw_key.end()) {
                query += " ?var_" + to_string(i);
            }
            else {
                query += " " + args[i];
            }
        }
        query += ")";
        auto res_ = ask(kb, query);
        if (res_.empty()) {
            add_predicate(kb, lit_);
        }
        else {
            for (int i = 0; i < args.size(); i++) {
            std:
                string tmp_pred = pred;
                for (int j = 0; j < args.size(); j++) {
                    tmp_pred += " " + res_[args[i]][j] + " ";
                }
            }
        }
    }

    kb.context.push_back(lit_);

    // add the closed world sentence
    if (!cw_key.empty()) {
        auto [pred, args] = parse_predicate(lit_);

        std::string cw_sen;
        std::string new_pred;
        int var_counter = 0;
        for (int i = 0; i < args.size(); i++) {
            auto date_types = kb.predicates[pred];
            if (std::find(cw_key.begin(), cw_key.end(), i) == cw_key.end()) {
                cw_sen = "forall ((cw_var_" + to_string(var_counter) + " " +
                         date_types[i] + ")) (=> (not (= cw_var_" +
                         to_string(var_counter) + " " + args[i] + ")) (not (";
                new_pred = "";
                if (!args.empty()) {
                    new_pred += pred + " ";
                }
                for (int j = 0; j < args.size(); j++) {
                    if (i != j) {
                        new_pred += args[j] + " ";
                    }
                    else {
                        new_pred += "cw_var_" + to_string(var_counter) + " ";
                    }
                }
                cw_sen += new_pred + ")))";
                kb.context.push_back(cw_sen);
                var_counter++;
            }
        }
    }
}

// This is part of my permutation algorithm for permuting the literals to get
// CNF from DNF c1 should get appended by each literal in c2, making
// c2.literals.size() number of output clauses example: c1: [a, b] | c2: [d,e]
// then output: [[a,d],[a,e], [b,d], [b,e]]
ast::CNF permute_step(Clause c1, Clause c2) {
    ast::Sentence for_cnf;
    ast::CNF output = ast::construct(for_cnf);
    output.conjunctionOfClauses.clear();
    Clause temp;
    for (Literal<Term> l : c2.literals) {
        temp.literals.insert(
            temp.literals.begin(), c1.literals.begin(), c1.literals.end());
        temp.literals.push_back(l); // append literal in c2 to c1
        output.conjunctionOfClauses.push_back(
            temp);             // append that new clause to CNF
        temp.literals.clear(); // reset the clause
    }
    return output;
}

// this method not's a CNF sentence
ast::CNF not_CNF(ast::CNF cnf) {
    // after not'ing the cnf we get a disjunction of conjuctions since all the
    // or's go to and's and vice versa. All the literals are not'd too
    for (int j = 0; j < cnf.conjunctionOfClauses.size(); j++) {
        for (int i = 0; i < cnf.conjunctionOfClauses.at(j).literals.size();
             i++) {
            if (cnf.conjunctionOfClauses.at(j).literals.at(i).is_negative ==
                false) {
                cnf.conjunctionOfClauses.at(j).literals.at(i).is_negative =
                    true;
            }
            else {
                cnf.conjunctionOfClauses.at(j).literals.at(i).is_negative =
                    false;
            }
        }
    }
    // after having swapped all the negations, we now interpret cnf as dnf, and
    // clause as a conjuction of literals not disjunction

    // the application of the distribution rule over the disjunctions and
    // conjuctions now results in taking one literal from each
    // "conjuctive-clause" in the dnf sentence and making a clause out of it,
    // and then permuting through all options conjucting each clause, which is a
    // cnf sentence at the end
    ast::Sentence for_cnf;
    ast::CNF temp1 = ast::construct(for_cnf);
    temp1.conjunctionOfClauses.clear();
    ast::CNF temp2 = ast::construct(
        for_cnf); // these are adding empty clauses, need to clear them
    temp2.conjunctionOfClauses.clear();
    ast::CNF output = ast::construct(for_cnf);
    for (Clause c : cnf.conjunctionOfClauses) {
        for (Clause c1 : output.conjunctionOfClauses) {
            temp1 = permute_step(c1, c);
            temp2.conjunctionOfClauses.insert(
                temp2.conjunctionOfClauses.end(),
                temp1.conjunctionOfClauses.begin(),
                temp1.conjunctionOfClauses.end());
            temp1.conjunctionOfClauses.clear();
        }
        output.conjunctionOfClauses.clear();
        output.conjunctionOfClauses.insert(output.conjunctionOfClauses.end(),
                                           temp2.conjunctionOfClauses.begin(),
                                           temp2.conjunctionOfClauses.end());
        temp2.conjunctionOfClauses.clear();
    }
    return output;
}

// This will be the ask function for non-variable resolution
// Have an overloaded ask, one that takes a parsed sentence and one that takes
// CNF sentence
// bool ask(KnowledgeBase& kb, ast::Sentence query) {
//    // convert the input query into CNF form
//    ast::CNF cnf_query =
//        ast::to_CNF(query); // does this convert it to a CNF too?
//    // now we not the input, note this causes an expoential increase in the
//    // sentence size, do I need a sentence to make CNF's?
//    ast::CNF query_clauses = not_CNF(cnf_query);
//
//    // we compile a large list of all clauses in KB, including one clause of
//    typedef vector<Clause> clause_vector;
//    clause_vector clause_vec;
//    clause_vector temp_vec;
//    clause_vector fact_vec;
//    Clause kb_facts, temp, resolvant;
//    // Each fact is a seperate clause
//    for (Literal<Term> l1 : kb.facts) {
//        kb_facts.literals.push_back(l1);
//        fact_vec.push_back(kb_facts);
//        kb_facts.literals.clear();
//    }
//    clause_vec.insert(clause_vec.end(), fact_vec.begin(), fact_vec.end());
//    // adding the clauses of the query
//    for (Clause c_q : query_clauses.conjunctionOfClauses) {
//        clause_vec.push_back(c_q);
//    }
//    // adding the rule clauses of the KB
//    for (Clause c_kb : kb.clauses) {
//        clause_vec.push_back(c_kb);
//    }
//
//    bool cond = false;
//    bool found = false;
//    // now to run the resolution
//    while (cond == false) {
//        for (int i = 0; i < clause_vec.size(); i++) {
//            for (int j = 0; j < clause_vec.size(); j++) {
//                if (i != j) {
//                    resolvant = clause_vec.at(i) == clause_vec.at(j);
//                    if (resolvant.literals.size() == 0) {
//                        return true;
//                    }
//                    else {
//                        for (Clause c_o : clause_vec) {
//                            bool vec_eq = false;
//                            int found_count = 0;
//                            if (resolvant.literals.size() ==
//                                c_o.literals.size()) {
//                                for (int l = 0; l < resolvant.literals.size();
//                                     l++) {
//                                    for (int ll = 0;
//                                         ll < resolvant.literals.size();
//                                         ll++) {
//                                        if (resolvant.literals.at(l) ==
//                                            c_o.literals.at(ll)) {
//                                            found_count = found_count + 1;
//                                            break;
//                                        }
//                                    }
//                                }
//                                if (found_count == resolvant.literals.size())
//                                {
//                                    vec_eq = true;
//                                }
//                            }
//                            if (vec_eq == true) {
//                                found =
//                                    true; // check if resolvant is a new
//                                    clause
//                            }
//                        }
//                        if (found == false) { // if new, add it to list
//                            temp_vec.push_back(resolvant);
//                        }
//                        found = false; // reset found condition
//                    }
//                }
//            }
//        }
//        // resolution fail condition is no new resolutions are produced, thus
//        KB
//        // is self consistant
//        if (temp_vec.size() ==
//            0) { // This should be the case that all resolvants have been
//            added
//                 // and no new ones are created
//            return false;
//            cond = true;
//        }
//        clause_vec.insert(clause_vec.end(), temp_vec.begin(), temp_vec.end());
//        temp_vec.clear();
//    }
//}
//// overloaded option for CNF input instead of parsed sentence
// bool ask(KnowledgeBase& kb, ast::CNF query) {
//     // convert the input query into CNF form
//     ast::CNF query_clauses = not_CNF(query);
//     // now to start the resolution inference algorithm, this is just checking
//     // clauses only need one clause to return empty because then the whole
//     // sentence is false, if want to check each clause, ask for each clause
//
//     // we compile a large list of all clauses in KB, including one clause of
//     typedef vector<Clause> clause_vector;
//     clause_vector clause_vec;
//     clause_vector temp_vec;
//     clause_vector fact_vec;
//     Clause kb_facts, temp, resolvant;
//     // Each fact is a seperate clause
//     for (Literal<Term> l1 : kb.facts) {
//         kb_facts.literals.push_back(l1);
//         fact_vec.push_back(kb_facts);
//         kb_facts.literals.clear();
//     }
//     clause_vec.insert(clause_vec.end(), fact_vec.begin(), fact_vec.end());
//     // adding the clauses of the query
//     for (Clause c_q : query_clauses.conjunctionOfClauses) {
//         clause_vec.push_back(c_q);
//     }
//     // adding the rule clauses of the KB
//     for (Clause c_kb : kb.clauses) {
//         clause_vec.push_back(c_kb);
//     }
//
//     bool cond = false;
//     bool found = false;
//     // now to run the resolution
//     while (cond == false) {
//         for (int i = 0; i < clause_vec.size(); i++) {
//             for (int j = 0; j < clause_vec.size(); j++) {
//                 if (i != j) {
//                     resolvant = clause_vec.at(i) == clause_vec.at(j);
//                     if (resolvant.literals.size() == 0) {
//                         return true;
//                         cond = true;
//                     }
//                     else {
//                         for (Clause c_o : clause_vec) {
//                             bool vec_eq = false;
//                             int found_count = 0;
//                             if (resolvant.literals.size() ==
//                                 c_o.literals.size()) {
//                                 for (int l = 0; l <
//                                 resolvant.literals.size();
//                                      l++) {
//                                     for (int ll = 0;
//                                          ll < resolvant.literals.size();
//                                          ll++) {
//                                         if (resolvant.literals.at(l) ==
//                                             c_o.literals.at(ll)) {
//                                             found_count = found_count + 1;
//                                             break;
//                                         }
//                                     }
//                                 }
//                                 if (found_count == resolvant.literals.size())
//                                 {
//                                     vec_eq = true;
//                                 }
//                             }
//                             if (vec_eq == true) {
//                                 found =
//                                     true; // check if resolvant is a new
//                                     clause
//                             }
//                         }
//                         if (found == false) { // if new, add it to list
//                             temp_vec.push_back(resolvant);
//                         }
//                         found = false; // reset found condition
//                     }
//                 }
//             }
//         }
//         // resolution fail condition is no new resolutions are produced, thus
//         KB
//         // is self consistant
//         if (temp_vec.size() ==
//             0) { // This should be the case that all resolvants have been
//             added
//                  // and no new ones are created
//             return false;
//             cond = true;
//         }
//         clause_vec.insert(clause_vec.end(), temp_vec.begin(),
//         temp_vec.end()); temp_vec.clear();
//     }
// }
//
// bool ask(KnowledgeBase& kb, string query) {
//
//     std::string kb_string = "";
//
//     vector<std::string> predicates;
//     vector<std::string> symbols;
//     std::string sub_kb_string = "";
//     for (auto f : kb.facts) {
//         if (std::find(predicates.begin(), predicates.end(), f.predicate) ==
//             predicates.end()) {
//             predicates.push_back(f.predicate);
//             sub_kb_string = "(declare-fun " + f.predicate + " (";
//             for (auto i = 0; i < f.args.size(); i++) {
//                 sub_kb_string += "Bool ";
//             }
//             sub_kb_string += ") Bool)";
//             kb_string += sub_kb_string;
//         }
//
//         for (auto a : f.args) {
//             if (std::find(symbols.begin(), symbols.end(), name(a)) ==
//                 symbols.end()) {
//                 symbols.push_back(name(a));
//                 sub_kb_string = "(declare-fun " + name(a) + " () Bool)";
//                 kb_string += sub_kb_string;
//             }
//         }
//
//         if (f.is_negative) {
//             sub_kb_string = "(assert (not (" + f.predicate;
//             for (auto a : f.args) {
//                 sub_kb_string += " " + name(a);
//             }
//             sub_kb_string += ")))";
//         }
//         else {
//             if (f.args.size() == 0) {
//                 sub_kb_string = "(assert " + f.predicate + ")";
//             }
//             else {
//                 sub_kb_string = "(assert (" + f.predicate;
//                 for (auto a : f.args) {
//                     sub_kb_string += " " + name(a);
//                 }
//                 sub_kb_string += "))";
//             }
//         }
//         kb_string += sub_kb_string;
//     }
//     std::string query_string = "(assert (not (" + query + ")))";
//     kb_string += query_string;
//     z3::context c;
//     z3::solver s(c);
//     s.from_string(kb_string.c_str());
//     switch (s.check()) {
//     case z3::unsat:
//         return TRUE;
//     case z3::sat:
//         return FALSE;
//     case z3::unknown:
//         return FALSE;
//     }
// }
//
// bool is_number(const std::string& s) {
//     return !s.empty() && std::find_if(s.begin(), s.end(), [](unsigned char c)
//     {
//                              return !std::isdigit(c);
//                          }) == s.end();
// }
//
// std::tuple<vector<std::string>, vector<std::string>, std::string>
// translate_kb(KnowledgeBase& kb) {
//     std::string kb_string = "";
//     std::string* p_kb_string = &kb_string;
//
//     vector<std::string> predicates;
//     vector<std::string> symbols;
//
//     return {predicates, symbols, kb_string};
// }
//
//// std::tuple<vector<std::string>, vector<std::string>, std::string>
//// translate_sentence(vector<std::string> predicates,
////                   vector<std::string> symbols,
////                   ast::Sentence sen) {
////     if (visit<ast::GetSentenceType>(sen) == "NotSentence") {
////         auto s_ = get<ast::NotSentence>(sen);
////         return visit<ast::NegationsIn>(s_.sentence);
////     }
////     std::string sub_kb_string = "";
////     if (std::find(predicates.begin(), predicates.end(), lit.predicate) ==
////         predicates.end()) {
////         predicates.push_back(lit.predicate);
////         sub_kb_string = "(declare-fun " + lit.predicate + " (";
////         for (auto a : lit.args) {
////             if (!is_number(name(a))) {
////                 sub_kb_string += "Bool ";
////             }
////             else {
////                 sub_kb_string += "Real ";
////             }
////         }
////         sub_kb_string += ") Bool)";
////     }
////
////     for (auto a : lit.args) {
////         if (!is_number(name(a))) {
////             if (std::find(symbols.begin(), symbols.end(), name(a)) ==
////                 symbols.end()) {
////                 symbols.push_back(name(a));
////                 sub_kb_string += "(declare-fun " + name(a) + " () Bool)";
////             }
////         }
////     }
////
////     if (lit.is_negative) {
////         if (lit.args.size() == 0) {
////             sub_kb_string = "(assert (not " + lit.predicate;
////             sub_kb_string += "))";
////         }
////         else {
////             sub_kb_string = "(assert (not (" + lit.predicate;
////             for (auto a : lit.args) {
////                 sub_kb_string += " " + name(a);
////             }
////             sub_kb_string += ")))";
////         }
////     }
////     else {
////         if (lit.args.size() == 0) {
////             sub_kb_string = "(assert " + lit.predicate + ")";
////         }
////         else {
////             sub_kb_string = "(assert (" + lit.predicate;
////             for (auto a : lit.args) {
////                 sub_kb_string += " " + name(a);
////             }
////             sub_kb_string += "))";
////         }
////     }
////     return {predicates, symbols, sub_kb_string};
//// }
////  now for the ask_vars method, which will return a substitution list for a
////  variable in the query, if resolute we do not have the standard aparting
////  implemented right now, we are operating on each variable input will have a
////  unqiue name
//
//// unless we restrict ourselves to horn clauses the inputs to the ask_vars
/// will / have to be a literal and it will just be unified against the facts of
/// the kb. / AIMA p.301 for detials.
//
//// UNDER CONSTRUCTION
//
//// This will return a vector of substitutions all of which are allowed for the
//// given input
///* ask_vars(KnowledgeBase& kb, Literal<Term> query) {
//    // sub_optional sub;
//    for(Literal lit : kb.facts) {
//        auto sub = unify(lit, query);
//    }
//    return sub;
//} */