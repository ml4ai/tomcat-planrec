#pragma once

#include <algorithm>
#include <string>

namespace fol {
    struct FOLDomain {
        int skolemConstantIndexical = 0;
        int skolemFunctionIndexical = 0;
        std::vector<std::string> constants;
        std::vector<std::string> functions;
        std::vector<std::string> predicates;

      public:
        FOLDomain(){}

        FOLDomain(std::vector<std::string> constants,
                  std::vector<std::string> functions,
                  std::vector<std::string> predicates) {
            this->constants = constants;
            this->functions = functions;
            this->constants = predicates;
        }

        static bool vec_contains(std::vector<std::string> v,
                                 const std::string& x) {
            if (std::find(v.begin(), v.end(), x) != v.end()) {
                return true;
            }
            else {
                return false;
            }
        }

        void addConstant(const std::string& constant) {
            this->constants.push_back(constant);
        }

        std::string addSkolemConstant() {
            std::string sc;
            do {
                sc = "SC" + std::to_string(this->skolemConstantIndexical++);
            } while (vec_contains(this->constants, sc) ||
                     vec_contains(this->functions, sc) ||
                     vec_contains(this->predicates, sc));

            addConstant(sc);
            return sc;
        }

        void addFunction(const std::string& function) {
            this->functions.push_back(function);
        }

        std::string addSkolemFunction() {
            std::string sf;
            do {
                sf = "SF" + std::to_string(this->skolemFunctionIndexical++);
            } while (vec_contains(this->constants, sf) ||
                     vec_contains(this->functions, sf) ||
                     vec_contains(this->predicates, sf));

            addFunction(sf);
            return sf;
        }

        void addPredicate(std::string predicate) {
            this->predicates.push_back(predicate);
        }
    };

} // namespace fol
