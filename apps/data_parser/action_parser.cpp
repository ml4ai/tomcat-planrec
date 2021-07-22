#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <string>
#include <sstream>
#include <iomanip>

using namespace std;
using json = nlohmann::json;

int missionTime2secElapsed(std::string str)
{
    stringstream ss;    
  
    /* Storing the whole string into string stream */
    ss << str;
  
    /* Running loop till the end of the stream */
    string temp;
    int a;
    int b;
    int count = 0;
    int num;
    while (!ss.eof()) {
  
        /* extracting word by word from stream */
        ss >> temp;
  
        /* Checking the given word is integer or not */
        if (stringstream(temp) >> num) {
          if (count == 0) {
            a = num;
            count++;
          }
          else {
            b = num;
            count++;
          }
        }
            
  
        /* To save from space at the end of string */
        temp = "";
    }
    return (900 - (a*60 + b));
}

json process_move_act(json& g) {
  json k;
  std::string move_act = "(!move,";
  move_act += g["data"]["playername"].get<std::string>();
  std::string exited;
  if (g["data"]["exited_locations"].size() == 2) {
    exited = g["data"]["exited_locations"][1]["id"].get<std::string>();
  }
  else {
    exited = g["data"]["exited_locations"][0]["id"].get<std::string>();
  }
  move_act += ",";
  move_act += exited;
  move_act += ",";
  if (g["data"].contains("locations")) {
    if (g["data"]["locations"].size() == 2) {
      move_act += g["data"]["locations"][1]["id"].get<std::string>();
    }
    else {
      move_act += g["data"]["locations"][0]["id"].get<std::string>();
    }
  }
  else {
    if (g["data"]["connections"][0]["connected_locations"][0] == exited) {
      move_act += g["data"]["connections"][0]["connected_locations"][1].get<std::string>();
    }
    else {
      move_act += g["data"]["connections"][0]["connected_locations"][0].get<std::string>();
    }
  }

  move_act += ",";
  std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          
  int time = missionTime2secElapsed(mission_time);

  move_act += std::to_string(time);

  move_act += ",";

  move_act += "0";

  move_act += ",)";

  k["task"] = move_act;
  return k;
}

json process_change_role_act(json& g) {
  json k;
  std::string act = "(!change_to_";

  act += g["data"]["new_role"].get<std::string>();
  act += ",";

  act += g["data"]["playername"].get<std::string>();
  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          
  int time = missionTime2secElapsed(mission_time);

  act += std::to_string(time);


  act += ",";
  act += "0,)";
  k["task"] = act;

  return k;

}

int main() {
  std::string msg;

  ifstream rfile("../apps/data_parser/study-2_2021.06_HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-2.metadata");
  json j;
  while(getline(rfile,msg)) {
    json g;
    g = json::parse(msg);
    if (g["data"]["mission_timer"] != "Mission Timer not initialized.") {
      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("exited_locations")) {
         j.push_back(process_move_act(g));
      }
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        j.push_back(process_change_role_act(g));
      } 
    }
  }

  rfile.close();

  std::ofstream o("test.json");
  o << std::setw(4) << j << std::endl;
  return EXIT_SUCCESS;
}
