#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <string>
#include <sstream>
#include <iomanip>
#include <unordered_map>
#include <vector>

using json = nlohmann::json;
struct Time {
  int hours;
  int minutes;
  double seconds;
  Time () {}
  Time (std::string ts_) {
    hours = std::stoi(ts_.substr(0,ts_.find(":")),nullptr);
    std::string ts1_ = ts_.substr(ts_.find(":") + 1);
    minutes = std::stoi(ts1_.substr(0,ts1_.find(":")),nullptr);
    std::string ts2_ = ts1_.substr(ts1_.find(":") + 1);
    seconds = std::stod(ts2_,nullptr);
  }
};

// Generate specific trace size from start
void fov_parser(std::string infile,
                std::string reffile,
                std::string outfile = "fov.json") {
  std::string imsg;
  std::string rmsg;
  std::ifstream ifile(infile);
  std::string init_timestamp;
  std::ifstream rfile(reffile);
  json objects;
  std::vector<std::string> agents;
  std::string player_key = "playername";
  while (getline(rfile,rmsg)) {
    json g;
    g = json::parse(rmsg);
    if (g["topic"] == "trial" && g["msg"]["sub_type"] == "start") {
      if(g["data"]["client_info"][0].find("playername") == g["data"]["client_info"][0].end()) {
        player_key = "participant_id";
      }
      for (auto a : g["data"]["client_info"]) {
        agents.push_back(a[player_key].get<std::string>());
      }
    }
    if (g["data"]["mission_state"] == "Start") {
      init_timestamp = g["msg"]["timestamp"].get<std::string>(); 
      break;
    }
  }
  init_timestamp = init_timestamp.substr(init_timestamp.find("T") + 1);
  Time init_t(init_timestamp.substr(0,init_timestamp.find("Z")));
  std::vector<int> seen;
  int step = -4;
  while(getline(ifile,imsg)) {
    json g;
    g = json::parse(imsg);
    if (g["msg"]["sub_type"] == "FoV") {
      std::string timestamp = g["msg"]["timestamp"].get<std::string>();
      std::string p = g["data"]["playername"].get<std::string>();
      std::string t1 = timestamp.substr(timestamp.find("T")+1);
      Time t(t1.substr(0,t1.find("Z")));
      int s = floor(((((t.hours - init_t.hours) * 3600) + ((t.minutes - init_t.minutes) * 60) + (t.seconds - init_t.seconds)) - 3));
      if (s != step) {
        seen = {};
        step = s;
        json count;
        for (auto a : agents) {
          count[a]["doors"] = 0;
          count[a]["blocks"] = 0;
          count[a]["reg_vics"] = 0;
          count[a]["crit_vics"] = 0;
          count[a]["timestep"] = s;
        }
        objects.push_back(count);
      }

      for (auto& e : g["data"]["blocks"]) {
        int id = e["id"].get<int>();
        bool not_found = std::find(seen.begin(),seen.end(),id) == seen.end();
        if (not_found) {
          seen.push_back(id);
          std::string type = e["type"].get<std::string>();
          if (type == "block_victim_1") {
            objects[s+3][p]["reg_vics"] = objects[s+3][p]["reg_vics"].get<int>() + 1;  
          }

          if (type == "block_victim_proximity") {
            objects[s+3][p]["crit_vics"] = objects[s+3][p]["crit_vics"].get<int>() + 1;
          }

          if (type == "gravel") {
            objects[s+3][p]["blocks"] = objects[s+3][p]["blocks"].get<int>() + 1;
          }

          if (type.find("_door") != std::string::npos) {
            objects[s+3][p]["doors"] = objects[s+3][p]["doors"].get<int>() + 1;
          }
        }
      }
    }
  }
  std::ofstream o(outfile);
  o << std::setw(4) << objects << std::endl;
}


