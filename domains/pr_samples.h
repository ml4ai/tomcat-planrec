#include <string>
#include <vector>
#include <unordered_map>

std::vector<std::string> delivery_sample= {"(drive truck_0 city_loc_2 city_loc_1)", 
                            "(pick_up truck_0 city_loc_1 package_0 capacity_1 capacity_2)", 
                            "(noop truck_0 city_loc_1)",
                            "(pick_up truck_0 city_loc_1 package_1 capacity_0 capacity_1)", 
                            "(drive truck_0 city_loc_1 city_loc_0)", 
                            "(drop truck_0 city_loc_0 package_0 capacity_0 capacity_1)", 
                            "(drive truck_0 city_loc_0 city_loc_2)", 
                            "(drop truck_0 city_loc_2 package_1 capacity_1 capacity_2)"};

std::unordered_map<std::string,std::vector<std::string>> pr_samples = {{"delivery_sample",delivery_sample}}; 
