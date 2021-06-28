#include "../Clause.h"
#include <string>
#include <vector>

/**
 * Conjunctive Normal Form (CNF) : a conjunction of clauses, where each clause
 * is a disjunction of literals.
 *
 * @author Ciaran O'Reilly
 *
 */
class CNF {

  private:
    std::vector<Clause> conjunctionOfClauses;

  public:
    CNF(std::vector<Clause> conjunctionOfClauses) {
        for (auto iter = conjunctionOfClauses.begin();
             iter != conjunctionOfClauses.end();
             ++iter) {
            this->conjunctionOfClauses.push_back(*iter);
        }
    }

  public:
    int getNumberOfClauses() { return this->conjunctionOfClauses.size(); }

  public:
    std::vector<Clause> getConjunctionOfClauses() {
        return this->conjunctionOfClauses;
    }

//  public:
//    //    std::to_string();
//    string to_string() {
//        std::string s = "";
//        for (int i = 0; i < this->conjunctionOfClauses.size(); i++) {
//            if (i > 0) {
//                s.append(",")
//            }
//            sb.append(this->conjunctionOfClauses[i].toString());
//        }
//
//        return sb;
//    }
};
