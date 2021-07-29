#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <string>
#include <sstream>
#include <iomanip>
#include <unordered_map>
#include <vector>
#include "../../planners/domains/team_sar.h"

using json = nlohmann::json;

struct j_node {
  json j;
  TeamSARState new_s;
  int endtime;
  int starttime;
};

int missionTime2secElapsed(std::string str)
{
  std::stringstream ss;    
  
    /* Storing the whole string into string stream */
    ss << str;
  
    /* Running loop till the end of the stream */
    std::string temp;
    int a;
    int b;
    int count = 0;
    int num;
    while (!ss.eof()) {
  
        /* extracting word by word from stream */
        ss >> temp;
  
        /* Checking the given word is integer or not */
        if (std::stringstream(temp) >> num) {
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

TeamSARState apply_operator(std::string action, TeamSARState& state, TeamSARDomain& domain, Args& args) {
  Operator<TeamSARState> op = domain.operators[action];
  std::optional<TeamSARState> newstate = op(state, args);
  return newstate.value();
}

j_node process_move_act(json& g, std::string c_loc, TeamSARState& state, TeamSARDomain& domain) {
  
  std::string action = "!move";

  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];

  act += ",";

  args["c_area"] = c_loc;

  act += args["c_area"];

  act += ",";

  args["n_area"] = g["data"]["locations"][0]["id"].get<std::string>();

  act += args["n_area"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          
  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  return n;
}

j_node process_change_role_act(json& g, TeamSARState& state, TeamSARDomain& domain) {
  std::string action = "!change_to_";
  Args args;
  std::string act = "(";

  action += g["data"]["new_role"].get<std::string>();

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];
  
  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          
  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  return n;
}

j_node process_triageReg_act(json& g, 
                             int start, 
                             std::unordered_map<std::string,std::string>& loc,
                             TeamSARState& state, 
                             TeamSARDomain& domain) {
  std::string action = "!triageReg";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];

  act += ",";

  act += loc[args["agent"]];

  act += ",";

  args["start"] = std::to_string(start);

  act += args["start"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int end = missionTime2secElapsed(mission_time);

  args["duration"] = std::to_string(end - start);

  act += args["duration"];

  act += ",)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = start;
  n.endtime = end;
  return n;
}

j_node process_triageCrit_act(json& g, 
                              int start, 
                              std::unordered_map<std::string,std::string>& loc,
                              TeamSARState& state,
                              TeamSARDomain& domain) {
  std::string action = "!triageCrit";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = loc[args["agent"]];

  act += args["area"];

  act += ",";

  args["start"] = std::to_string(start);

  act += args["start"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int end = missionTime2secElapsed(mission_time);

  args["duration"] = std::to_string(end - start);

  act += args["duration"];

  act += ",)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = start;
  n.endtime = end;
  return n;
}

j_node process_wakeCrit_act(json& g, 
                          std::vector<std::string>& agents, 
                          std::unordered_map<std::string,std::string>& c_loc,
                          TeamSARState& state,
                          TeamSARDomain& domain) {

  std::string action = "!wakeCrit";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";
  
  args["agent1"] = agents[0];

  args["agent2"] = agents[1];

  args["agent3"] = agents[2];

  act += args["agent1"];

  act += ",";

  act += args["agent2"];

  act += ",";

  act += args["agent3"];

  act += ",";

  args["area"] = c_loc[agents[0]];

  act += args["area"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  return n;
}

j_node process_pickUpVic_act(json& g, 
                             std::unordered_map<std::string,std::string>& c_loc,
                             TeamSARState& state,
                             TeamSARDomain& domain) {
  std::string action = "!pickup_vic";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = c_loc[args["agent"]];

  act += args["area"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  return n;
}

j_node process_putDownVic_act(json& g, 
                             std::unordered_map<std::string,std::string>& c_loc,
                             TeamSARState& state,
                             TeamSARDomain& domain) {
  std::string action = "!put_down_vic";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = c_loc[args["agent"]];

  act += args["area"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  return n;
}

j_node process_breakBlock_act(json& g, 
                             std::unordered_map<std::string,std::string>& c_loc,
                             TeamSARState& state,
                             TeamSARDomain& domain) {
  std::string action = "!breakBlock";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"]["playername"].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = c_loc[args["agent"]];

  act += args["area"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  return n;
}

json add_search_act(std::string agent, std::string area, int start, int end) {
  std::string act = "(!search,";
  
  act += agent;

  act += ",";

  act += area;

  act += ",";

  act += std::to_string(start);

  act += ",";

  act += std::to_string(end - start);

  act += ",)";

  json k;

  k["task"] = act;

  return k;
}

j_node add_exit(std::string a, TeamSARState& state, TeamSARDomain& domain) {
  std::string action = "!exit";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = a;

  act += args["agent"];

  act += ",";

  args["start"] = "900";

  act += "900";

  act += ",";

  args["duration"] = "0";

  act += "0";

  act += ",)";

  j_node n;
  n.j["pre-state"] = state.to_json();
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.j["post-state"] = newstate.to_json();
  n.new_s = newstate;
  n.starttime = 900;
  n.endtime = 900;
  return n;
}

json team_sar_parser(std::string infile,
                     TeamSARState state,
                     TeamSARDomain& domain,
                     bool gen_file = false,
                     std::string outfile = "parsed_plan_trace.json") {
  std::string msg;

  std::ifstream rfile(infile);
  json j;
  std::unordered_map<std::string,int> regTriageTime;
  std::unordered_map<std::string,int> critTriageTime;
  std::vector<std::string> agents = {};
  std::unordered_map<std::string,std::string> c_loc;
//  std::unordered_map<std::string,int> prev_act_endtime;
  while(getline(rfile,msg)) {
    json g;
    g = json::parse(msg);

    if (g["msg"]["sub_type"] == "start") {
      for (auto a : g["data"]["client_info"]) {
        agents.push_back(a["playername"].get<std::string>());
        c_loc[a["playername"].get<std::string>()] = "NONE";
        regTriageTime[a["playername"].get<std::string>()] = 0;
        critTriageTime[a["playername"].get<std::string>()] = 0;
//        prev_act_endtime[a["playername"].get<std::string>()] = -1;
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
            j_node n = process_move_act(g,c_loc[agents[0]],state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[0]] = n.endtime;
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
            j_node n = process_move_act(g,c_loc[agents[1]],state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[1]] = n.endtime;
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
            j_node n = process_move_act(g,c_loc[agents[2]],state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[2]] = n.endtime;
            c_loc[agents[2]] = g["data"]["locations"][0]["id"];
          }
        }
      }
 
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        std::string p = g["data"]["playername"].get<std::string>();
        j_node n = process_change_role_act(g,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        j.push_back(n.j);
        state = n.new_s;
//        prev_act_endtime[p] = n.endtime;
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
            j_node n = process_triageReg_act(g,regTriageTime[agents[0]],c_loc,state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[0]] = n.endtime;
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
            j_node n = process_triageReg_act(g,regTriageTime[agents[1]],c_loc,state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[1]] = n.endtime;
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
            j_node n = process_triageReg_act(g,regTriageTime[agents[2]],c_loc,state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[2]] = n.endtime;
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
            j_node n = process_triageCrit_act(g,critTriageTime[agents[0]],c_loc,state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[0]] = n.endtime;
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
            j_node n = process_triageCrit_act(g,critTriageTime[agents[1]],c_loc,state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[1]] = n.endtime;
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
            j_node n = process_triageCrit_act(g,critTriageTime[agents[2]],c_loc,state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            j.push_back(n.j);
            state = n.new_s;
//            prev_act_endtime[agents[2]] = n.endtime;
          }
          critTriageTime[agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:ProximityBlockInteraction" &&
           g["data"]["players_in_range"] == 3 &&
           g["data"]["action_type"] == "ENTERED_RANGE") {
        j_node n = process_wakeCrit_act(g,agents,c_loc,state,domain);
//        for (auto a : agents) {
//          if (prev_act_endtime[a] != -1) {
//            if (n.starttime > prev_act_endtime[a]) {
//              j.push_back(add_search_act(a,c_loc[a],prev_act_endtime[a],n.starttime));
//            }
//          }
//          prev_act_endtime[a] = n.endtime;
//        }
        j.push_back(n.j);
        state = n.new_s;
      }  

      if (g["msg"]["sub_type"] == "Event:VictimPickedUp") {
        std::string p = g["data"]["playername"].get<std::string>();
        j_node n = process_pickUpVic_act(g,c_loc,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        j.push_back(n.j);
        state = n.new_s;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:VictimPlaced") {
        std::string p = g["data"]["playername"].get<std::string>();
        j_node n = process_putDownVic_act(g,c_loc,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        j.push_back(n.j);
        state = n.new_s;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:RubbleDestroyed") {
        std::string p = g["data"]["playername"].get<std::string>();
        j_node n = process_breakBlock_act(g,c_loc,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        j.push_back(n.j);
        state = n.new_s;
//        prev_act_endtime[p] = n.endtime;
      }
    }
  }
  for (auto a : agents) {
    j_node n = add_exit(a,state,domain);

    j.push_back(n.j);
    state = n.new_s;
  } 

  rfile.close();
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << j << std::endl;
  }

  return j;
}
