#include <nlohmann/json.hpp>
#include <vector>
#include "util.h"

using json = nlohmann::json;

struct mission_map {
  std::unordered_map<std::string, std::vector<std::string>> graph;
  std::vector<std::string> zones;
  std::vector<std::string> rooms;
};

mission_map 
parse_map_from_json(json j, std::vector<std::string> alt_zones = {}) {

  mission_map mp;
  for (auto& e : j["locations"]) {
    if (e["type"] == "room" || 
        e["type"] == "hallway" || 
        e["type"] == "bathroom") {
      if (e["type"] != "hallway" &&
         !in(e["id"].get<std::string>(),alt_zones)) {
        mp.rooms.push_back(e["id"]);
      }
      if (e["id"] != "loc_42") {
        mp.zones.push_back(e["id"]);
        mp.graph[e["id"].get<std::string>()] = {};
        for (auto& c : j["connections"]) {
          if (c["type"] != "extension") {
            bool found_loc = false;
            std::vector<std::string> cns;
            for (auto& loc : c["connected_locations"]) {
              if (loc == e["id"]) {
                found_loc = true;
                continue;
              }
              if (e.find("child_locations") != e.end()) {
                for (auto& cl : e["child_locations"]) {
                  if (loc == cl) {
                    found_loc = true;
                    continue;
                  }
                }
              }
              for (auto& l : j["locations"]) {
                if (l["type"] == "room" ||
                    l["type"] == "hallway" ||
                    l["type"] == "bathroom") {
                  if(l.find("child_locations") != l.end()) {
                    for(auto& lcl : l["child_locations"]) {
                      if (loc == lcl) {
                        if(!in(l["id"].get<std::string>(),cns)) {
                          cns.push_back(l["id"].get<std::string>());
                        }
                      }
                    }
                  }
                  if (l["id"] == loc) {
                    if(!in(loc.get<std::string>(),cns)) {
                      cns.push_back(loc.get<std::string>());
                    }
                  }
                }
              }
            } 
            if (found_loc && !cns.empty()) {
              for (auto fl : cns) {
                if(!in(fl,mp.graph[e["id"].get<std::string>()]) && fl != e["id"]) {
                  mp.graph[e["id"].get<std::string>()].push_back(fl);
                }
              }
            }
          }
        }
      }
    }
  }
  return mp;
}
