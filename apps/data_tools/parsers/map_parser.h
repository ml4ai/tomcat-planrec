#include <boost/json.hpp>
#include <vector>
#include "util.h"

namespace json = boost::json;

struct mission_map {
  std::unordered_map<std::string, std::vector<std::string>> graph;
  std::vector<std::string> zones;
  std::vector<std::string> rooms;
};

mission_map 
parse_map_from_json(json::value j) {

  mission_map mp;
  for (auto& e : j.as_object()["locations"].as_array()) {
    if ((e.as_object()["type"].as_string() == "room" || 
        e.as_object()["type"].as_string() == "hallway" || 
        e.as_object()["type"].as_string() == "bathroom") &&
        e.as_object()["name"].as_string() != "UNKNOWN") {
      if (e.as_object()["type"].as_string() != "hallway") {
        mp.rooms.push_back(json::value_to<std::string>(e.as_object()["id"]));
      }
      mp.zones.push_back(json::value_to<std::string>(e.as_object()["id"]));
      mp.graph[json::value_to<std::string>(e.as_object()["id"])] = {};
      for (auto& c : j.as_object()["connections"].as_array()) {
        if (c.as_object()["type"].as_string() != "extension") {
          bool found_loc = false;
          std::vector<std::string> cns;
          for (auto& loc : c.as_object()["connected_locations"].as_array()) {
            if (loc.as_string() == e.as_object()["id"].as_string()) {
              found_loc = true;
              continue;
            }
            if (e.as_object().find("child_locations") != e.as_object().end()) {
              for (auto& cl : e.as_object()["child_locations"].as_array()) {
                if (loc.as_string() == cl.as_string()) {
                  found_loc = true;
                  continue;
                }
              }
            }
            for (auto& l : j.as_object()["locations"].as_array()) {
              if (l.as_object()["type"].as_string() == "room" ||
                  l.as_object()["type"].as_string() == "hallway" ||
                  l.as_object()["type"].as_string() == "bathroom") {
                if(l.as_object().find("child_locations") != l.as_object().end()) {
                  for(auto& lcl : l.as_object()["child_locations"].as_array()) {
                    if (loc.as_string() == lcl.as_string()) {
                      if(!in(json::value_to<std::string>(l.as_object()["id"]),cns)) {
                        cns.push_back(json::value_to<std::string>(l.as_object()["id"]));
                      }
                    }
                  }
                }
                if (l.as_object()["id"].as_string() == loc.as_string()) {
                  if(!in(json::value_to<std::string>(loc),cns)) {
                    cns.push_back(json::value_to<std::string>(loc));
                  }
                }
              }
            }
          } 
          if (found_loc && !cns.empty()) {
            for (auto fl : cns) {
              if(!in(fl,mp.graph[json::value_to<std::string>(e.as_object()["id"])]) && fl != e.as_object()["id"].as_string()) {
                mp.graph[json::value_to<std::string>(e.as_object()["id"])].push_back(fl);
              }
            }
          }
        }
      }
    }
  }
  return mp;
}
