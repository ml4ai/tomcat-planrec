#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <string>
#include <sstream>
#include <iomanip>
#include <unordered_map>
#include <vector>

using namespace std;
using json = nlohmann::json;

struct j_loc {
  json j;
  std::string loc;
};

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

j_loc process_move_act(json& g) {
  json k;
  std::string current_loc;
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
      current_loc = g["data"]["locations"][1]["id"].get<std::string>();
      move_act += current_loc;
    }
    else {
      current_loc = g["data"]["locations"][0]["id"].get<std::string>();
      move_act += current_loc;
    }
  }
  else {
    if (g["data"]["connections"][0]["connected_locations"][0] == exited) {
      current_loc = g["data"]["connections"][0]["connected_locations"][1].get<std::string>();
      move_act += current_loc;
    }
    else {
      current_loc = g["data"]["connections"][0]["connected_locations"][0].get<std::string>();
      move_act += current_loc;
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
  j_loc n;
  n.j = k;
  n.loc = current_loc;
  return n;
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

json process_triageReg_act(json& g, int start, std::unordered_map<std::string,std::string>& loc) {
  json k;
  std::string act = "(!triageReg,";

  std::string player = g["data"]["playername"].get<std::string>();
  act += player;

  act += ",";

  act += loc[player];

  act += ",";

  act += std::to_string(start);

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int end = missionTime2secElapsed(mission_time);

  act += std::to_string(end - start);

  act += ",)";

  k["task"] = act;

  return k;
}

json process_triageCrit_act(json& g, 
                            int start, 
                            std::unordered_map<std::string,std::string>& loc,
                            std::vector<std::string>& agents) {
  json k;
  std::string act = "(!triageCrit,";

  std::string player = g["data"]["playername"].get<std::string>();
  act += player;

  act += ",";

  for (auto a : agents) {
    if (a != player) {
      act += a;
      act += ",";
    }
  }

  act += loc[player];

  act += ",";

  act += std::to_string(start);

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int end = missionTime2secElapsed(mission_time);

  act += std::to_string(end - start);

  act += ",)";

  k["task"] = act;

  return k;
}

int main() {
  std::string msg;

  ifstream rfile("../apps/data_parser/study-2_2021.06_HSRData_TrialMessages_Trial-T000485_Team-TM000143_Member-na_CondBtwn-2_CondWin-SaturnA_Vers-2.metadata");
  json j;
  std::unordered_map<std::string,int> regTriageTime;
  std::unordered_map<std::string,int> critTriageTime;
  std::vector<std::string> agents = {};
  std::unordered_map<std::string,std::string> c_loc;
  while(getline(rfile,msg)) {
    json g;
    g = json::parse(msg);

    if (g["msg"]["sub_type"] == "start") {
      for (auto a : g["data"]["client_info"]) {
        agents.push_back(a["playername"].get<std::string>());
        c_loc[a["playername"].get<std::string>()] = "NONE";
        regTriageTime[a["playername"].get<std::string>()] = 0;
        critTriageTime[a["playername"].get<std::string>()] = 0;
      }
    }
    if (g["data"]["mission_timer"] != "Mission Timer not initialized.") {
      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("exited_locations")) {
         j_loc n = process_move_act(g);
         c_loc[g["data"]["playername"].get<std::string>()] = n.loc;
         j.push_back(n.j);
      }
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        j.push_back(process_change_role_act(g));
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"]["playername"] == agents[0]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[agents[0]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j.push_back(process_triageReg_act(g,regTriageTime[agents[0]],c_loc));
          }
          regTriageTime[agents[0]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"]["playername"] == agents[1]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[agents[1]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j.push_back(process_triageReg_act(g,regTriageTime[agents[1]],c_loc));
          }
          regTriageTime[agents[1]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"]["playername"] == agents[2]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[agents[2]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j.push_back(process_triageReg_act(g,regTriageTime[agents[2]],c_loc));
          }
          regTriageTime[agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"]["playername"] == agents[0]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[agents[0]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j.push_back(process_triageCrit_act(g,critTriageTime[agents[0]],c_loc,agents));
          }
          critTriageTime[agents[0]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"]["playername"] == agents[1]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[agents[1]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j.push_back(process_triageCrit_act(g,critTriageTime[agents[1]],c_loc,agents));
          }
          critTriageTime[agents[1]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"]["playername"] == agents[2]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[agents[2]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j.push_back(process_triageCrit_act(g,critTriageTime[agents[2]],c_loc,agents));
          }
          critTriageTime[agents[2]] = 0;
        }
      }


    }
  }

  rfile.close();

  std::ofstream o("test.json");
  o << std::setw(4) << j << std::endl;
  return EXIT_SUCCESS;
}
