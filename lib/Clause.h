#pragma once

#include <vector>
#include "unification.h"
#include "parsing/ast.hpp"

struct Clause {
    std::vector<ast::Literal<ast::Term>> literals;

    // this will run a binary inference between the 2 clauses and return the resulting clause (an empty clause means these clauses are in contradiction)
    friend Clause operator==(const Clause& lhs, const Clause& rhs) {
        typedef std::vector<ast::Literal<ast::Term>> lits;
        Clause resolvant;
        lits pos_lits_rhs;
        lits neg_lits_rhs;
        lits pos_lits_lhs;
        lits neg_lits_lhs;

        // create the list of positive and negative literals for each clause
        for (ast::Literal<ast::Term> l1 : rhs.literals ) {
            if(l1.is_negative) {
                neg_lits_rhs.push_back(l1);
            }
            else {
                pos_lits_rhs.push_back(l1);
            }
        }
        for (ast::Literal<ast::Term> l2 : lhs.literals) {
            if(l2.is_negative) {
                neg_lits_lhs.push_back(l2);
            }
            else {
                pos_lits_lhs.push_back(l2);
            }
        }

        lits t_pos_lits;
        lits t_neg_lits;
        lits resolvant_lits;

        // this loop will first try and resolve the rhs_pos with the lhs_neg and then the rhs_neg with the lhs_pos
        for (int i=0; i<2; i++) {
            t_pos_lits.clear();
            t_neg_lits.clear();

            if (i==0) {
                t_pos_lits.insert(t_pos_lits.end(), pos_lits_rhs.begin(), pos_lits_rhs.end());
                t_neg_lits.insert(t_neg_lits.end(), neg_lits_lhs.begin(), neg_lits_lhs.end());
            }
            else {
                t_pos_lits.insert(t_pos_lits.end(), pos_lits_lhs.begin(), pos_lits_lhs.end());
                t_neg_lits.insert(t_neg_lits.end(), neg_lits_rhs.begin(), neg_lits_rhs.end());                
            }
            for(ast::Literal<ast::Term> litp : t_pos_lits) {
                bool found=false;
                for(ast::Literal litn : t_neg_lits) {
                    if(litp == litn) {
                        found = true;
                    }
                }
                if(found == false) {
                    resolvant_lits.push_back(litp); // if there was no matching negative literal to cancel the positive add it to list
                }
            }
            for(ast::Literal<ast::Term> litn : t_neg_lits) {
                bool found=false;
                for(ast::Literal litp : t_pos_lits) {
                    if(litp == litn) {
                        found = true;
                    }
                }
                if(found == false) {
                    resolvant_lits.push_back(litn); // if there was no matching positive literal to cancel the negative add it to list
                }
            }
        }

        // now we remove any duplicates by converting to a set and then back (assuming the resolvant isn't empty) and create our resolvant clause
        if(resolvant_lits.size()>0) {
            for (int i=0; i < resolvant_lits.size(); i++) {
                for (int j=0; j < resolvant_lits.size(); j++) {
                    if (i!=j) {
                        if (resolvant_lits.at(i)==resolvant_lits.at(j)) {
                            resolvant_lits.erase(resolvant_lits.begin()+j);
                        }
                    }
                }
            }
            // now to construct the resolvant clause
            resolvant.literals.insert(resolvant.literals.end(), resolvant_lits.begin(), resolvant_lits.end());
        }

        return resolvant;
    }
};
