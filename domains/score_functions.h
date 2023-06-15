#include "typedefs.h"
#include <string>
#include <algorithm>


double delivery_one(KnowledgeBase& kb,std::vector<std::string>& plan) {
  int move_count = 0;
  for (auto const& a : plan) {
    if (a.find("drive") != std::string::npos) {
      move_count++;
    }
  }
  if (kb.ask("(and (at package_0 city_loc_0) (at package_1 city_loc_2))")) {
    return 1.0*(1.0/(1.0 + move_count))*(1.0/(1 + plan.size()));
  }
  if (kb.ask("(capacity truck_0 capacity_0)")) {
    return 0.5*(1.0/(1.0 + move_count));
  }
  return 0.0;
}

double delivery_one_rec(KnowledgeBase& kb,std::vector<std::string>& plan) {
  return 1.0;
}

double simple(KnowledgeBase& kb, std::vector<std::string>& plan) {
  return 1.0;
}

double travel_one(KnowledgeBase& kb, std::vector<std::string>& plan) {
  if (kb.ask("(and (loc me park) (cash me twenty))")) {
    return 1;
  }
  if (kb.ask("(loc me park)")) {
    return 0.5;
  }
  return 0.0;
}

double sar3(KnowledgeBase& kb, std::vector<std::string>& plan) {
  auto facts = kb.get_facts();
  double c_vic_count = 0.0;
  if (facts.find("vic_is_type_C") != facts.end()) {
    for (auto const& p : facts["vic_is_type_C"]) {
      c_vic_count += 1.0; 
    }
  }
  double r_vic_count = 0.0;
  if (facts.find("vic_is_type_A") != facts.end()) {
    for (auto const& p : facts["vic_is_type_A"]) {
      r_vic_count += 1.0;
    }
  }
  if (facts.find("vic_is_type_B") != facts.end()) {
    for (auto const& p : facts["vic_is_type_B"]) {
      r_vic_count += 1.0;
    }
  }
  double c_res = 0.0;
  if (facts.find("rescued_c") != facts.end()) {
    for (auto const& p : facts["rescued_c"]) {
      c_res += 1.0;
    }
  }
  double r_res = 0.0;
  if (facts.find("rescued_c") != facts.end()) {
    for (auto const& p : facts["rescued_r"]) {
      r_res += 1.0;
    }
  }
  double p_total = c_vic_count*50.0 + r_vic_count*10.0;
  double points = c_res*50.0 + r_res*10.0;
  return points/p_total;
}

Scorers scorers = Scorers({{"delivery_one", delivery_one},
                           {"delivery_one_rec",delivery_one_rec},
                           {"travel_one", travel_one},
                           {"sar3",sar3},
                           {"simple", simple}});
