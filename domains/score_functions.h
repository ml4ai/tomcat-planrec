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

Scorers scorers = Scorers({{"delivery_one", delivery_one},
                           {"travel_one", travel_one},
                           {"simple", simple}});
