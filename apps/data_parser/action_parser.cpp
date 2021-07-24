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

json process_move_act(json& g, std::string c_loc) {
  json k;
  
  std::string act = "(!move,";

  act += g["data"]["playername"].get<std::string>();

  act += ",";

  act += c_loc;

  act += ",";

  act += g["data"]["locations"][0]["id"].get<std::string>();

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          
  int time = missionTime2secElapsed(mission_time);

  act += std::to_string(time);

  act += ",";

  act += "0,)";

  k["task"] = act;
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
                            std::unordered_map<std::string,std::string>& loc) {
  json k;
  std::string act = "(!triageCrit,";

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

json process_wakeCrit_act(json& g, 
                          std::vector<std::string>& agents, 
                          std::unordered_map<std::string,std::string>& c_loc) {
  json k;
  std::string act = "(!wakeCrit,";

  for (auto a : agents) {
    act += a;
    act += ",";
  }

  act += c_loc[agents[0]];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int start = missionTime2secElapsed(mission_time);

  act += std::to_string(start);

  act += ",";

  act += "0,)";

  k["task"] = act;

  return k;
}

json process_pickUpVic_act(json& g, std::unordered_map<std::string,std::string>& c_loc) {
  json k;
  std::string act = "(!pickup_vic,";

  std::string player = g["data"]["playername"].get<std::string>();

  act += player;

  act += ",";

  act += c_loc[player];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int start = missionTime2secElapsed(mission_time);

  act += std::to_string(start);

  act += ",";

  act += "0,)";

  k["task"] = act;

  return k;

}

json process_putDownVic_act(json& g, std::unordered_map<std::string,std::string>& c_loc) {
  json k;
  std::string act = "(!put_down_vic,";

  std::string player = g["data"]["playername"].get<std::string>();

  act += player;

  act += ",";

  act += c_loc[player];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int start = missionTime2secElapsed(mission_time);

  act += std::to_string(start);

  act += ",";

  act += "0,)";

  k["task"] = act;

  return k;

}

json process_breakBlock_act(json& g, std::unordered_map<std::string,std::string>& c_loc) {
  json k;
  std::string act = "(!break_block,";

  std::string player = g["data"]["playername"].get<std::string>();

  act += player;

  act += ",";

  act += c_loc[player];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int start = missionTime2secElapsed(mission_time);

  act += std::to_string(start);

  act += ",";

  act += "0,)";

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
          g["data"].contains("locations") &&
          g["data"]["playername"] == agents[0]) {
        if (c_loc[agents[0]] == "NONE") {
          c_loc[agents[0]] = g["data"]["locations"][0]["id"].get<std::string>();  
        }
        else {
          if (g["data"]["locations"][0]["id"] != c_loc[agents[0]]) {
            j.push_back(process_move_act(g,c_loc[agents[0]]));
            c_loc[agents[0]] = g["data"]["locations"][0]["id"];
          }
        }
      }

      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"]["playername"] == agents[1]) {
        if (c_loc[agents[1]] == "NONE") {
          c_loc[agents[1]] = g["data"]["locations"][0]["id"].get<std::string>();  
        }
        else {
          if (g["data"]["locations"][0]["id"] != c_loc[agents[1]]) {
            j.push_back(process_move_act(g,c_loc[agents[1]]));
            c_loc[agents[1]] = g["data"]["locations"][0]["id"];
          }
        }
      }

      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"]["playername"] == agents[2]) {
        if (c_loc[agents[2]] == "NONE") {
          c_loc[agents[2]] = g["data"]["locations"][0]["id"].get<std::string>();  
        }
        else {
          if (g["data"]["locations"][0]["id"] != c_loc[agents[2]]) {
            j.push_back(process_move_act(g,c_loc[agents[2]]));
            c_loc[agents[2]] = g["data"]["locations"][0]["id"];
          }
        }
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
            j.push_back(process_triageCrit_act(g,critTriageTime[agents[0]],c_loc));
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
            j.push_back(process_triageCrit_act(g,critTriageTime[agents[1]],c_loc));
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
            j.push_back(process_triageCrit_act(g,critTriageTime[agents[2]],c_loc));
          }
          critTriageTime[agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:ProximityBlockInteraction" &&
           g["data"]["players_in_range"] == 3 &&
           g["data"]["action_type"] == "ENTERED_RANGE") {
        j.push_back(process_wakeCrit_act(g,agents,c_loc));
      }  

      if (g["msg"]["sub_type"] == "Event:VictimPickedUp") {
        j.push_back(process_pickUpVic_act(g,c_loc));
      }

      if (g["msg"]["sub_type"] == "Event:VictimPlaced") {
        j.push_back(process_putDownVic_act(g,c_loc));
      }

      if (g["msg"]["sub_type"] == "Event:RubbleDestroyed") {
        j.push_back(process_breakBlock_act(g,c_loc));
      }
 
    }
  }

  rfile.close();

  std::ofstream o("test.json");
  o << std::setw(4) << j << std::endl;
  return EXIT_SUCCESS;
}
