#include <string>
#include <vector>
#include <unordered_map>

std::vector<std::pair<std::string,std::string>> delivery_sample= {{"drive","(drive truck_0 city_loc_2 city_loc_1)"}, 
  {"pick_up","(pick_up truck_0 city_loc_1 package_0 capacity_1 capacity_2)"}, 
  {"noop","(noop truck_0 city_loc_1)"},
  {"pick_up","(pick_up truck_0 city_loc_1 package_1 capacity_0 capacity_1)"}, 
  {"drive","(drive truck_0 city_loc_1 city_loc_0)"}, 
  {"drop","(drop truck_0 city_loc_0 package_0 capacity_0 capacity_1)"}, 
  {"drive","(drive truck_0 city_loc_0 city_loc_2)"}, 
  {"drop","(drop truck_0 city_loc_2 package_1 capacity_1 capacity_2)"}};

std::unordered_map<std::string,std::vector<std::pair<std::string,std::string>>> pr_samples = {{"delivery_sample",delivery_sample}}; 
