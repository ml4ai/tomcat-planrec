#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <string>
#include <sstream>
#include <iomanip>
#include <unordered_map>
#include <vector>
#include "../../planners/domains/vanilla_team_sar.h"

using json = nlohmann::json;

struct j_node {
  json j;
  TeamSARState new_s;
  Action action;
  int endtime;
  int starttime;
};

struct parse_data {
  json trace;
  TeamSARState initial_state;
  std::unordered_map<std::string,std::vector<Action>> action_tracker;
  std::unordered_map<std::string,std::vector<std::string>> loc_tracker;
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
  if (newstate) {
    return newstate.value();
  }
  std::string message = action;
  message += " preconditions failed during parsing!";
  throw std::logic_error(message);
}

j_node process_move_act(json& g, std::string player_key, TeamSARState& state, TeamSARDomain& domain) {
  
  std::string action = "!move";

  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["c_area"] = state.agent_loc[args["agent"]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["c_area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_change_role_act(json& g, std::string player_key, TeamSARState& state, TeamSARDomain& domain) {
  std::string action = "!change_to_";
  Args args;
  std::string act = "(";

  action += g["data"]["new_role"].get<std::string>();

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = state.change_zone;
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_triageReg_act(json& g,
                             std::string player_key,
                             int start, 
                             TeamSARState& state, 
                             TeamSARDomain& domain) {
  std::string action = "!triageReg";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = state.agent_loc[args["agent"]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = start;
  n.endtime = end;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_triageCrit_act(json& g,
                              std::string player_key,
                              int start, 
                              TeamSARState& state,
                              TeamSARDomain& domain) {
  std::string action = "!triageCrit";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = state.agent_loc[args["agent"]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = start;
  n.endtime = end;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_wakeCrit_act(json& g, 
                            TeamSARState& state,
                            TeamSARDomain& domain) {
  std::string action = "!wakeCrit";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";
  
  args["agent1"] = state.agents[0];

  args["agent2"] = state.agents[1];

  args["agent3"] = state.agents[2];

  act += args["agent1"];

  act += ",";

  act += args["agent2"];

  act += ",";

  act += args["agent3"];

  act += ",";

  args["area"] = state.agent_loc[state.agents[0]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = "all";
  n.action.area = args["area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_pickUpVic_act(json& g, 
                             std::string player_key,
                             TeamSARState& state,
                             TeamSARDomain& domain) {
  std::string action = "!pickup_vic";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = state.agent_loc[args["agent"]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_putDownVic_act(json& g, 
                              std::string player_key,
                              TeamSARState& state,
                              TeamSARDomain& domain) {
  std::string action = "!put_down_vic";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = state.agent_loc[args["agent"]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_breakBlock_act(json& g, 
                              std::string player_key,
                              TeamSARState& state,
                              TeamSARDomain& domain) {
  std::string action = "!break_block";
  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area"] = state.agent_loc[args["agent"]];

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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_markOpening_act(json& g, 
                              std::string player_key,
                              std::string area_marked,
                              TeamSARState& state,
                              TeamSARDomain& domain) {
  std::string action = "!mark_opening_";
  if (g["data"]["type"] == "Marker Block 1") {
    action += "1";
  }

  if (g["data"]["type"] == "Marker Block 2") {
    action += "2";
  }

  if (g["data"]["type"] == "Marker Block 3") {
    action += "3";
  }

  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area_placed"] = state.agent_loc[args["agent"]];

  act += args["area_placed"];

  act += ",";

  args["area_marked"] = area_marked;

  act += args["area_marked"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area_placed"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

j_node process_markArea_act(json& g, 
                            std::string player_key,
                            TeamSARState& state,
                            TeamSARDomain& domain) {
  std::string action = "!mark_area_";
  if (g["data"]["type"] == "Marker Block 1") {
    action += "1";
  }

  if (g["data"]["type"] == "Marker Block 2") {
    action += "2";
  }

  if (g["data"]["type"] == "Marker Block 3") {
    action += "3";
  }

  Args args;

  std::string act = "(";

  act += action;

  act += ",";

  args["agent"] = g["data"][player_key].get<std::string>();

  act += args["agent"];

  act += ",";

  args["area_marked"] = state.agent_loc[args["agent"]];

  act += args["area_marked"];

  act += ",";

  std::string mission_time = g["data"]["mission_timer"].get<std::string>();

  int time = missionTime2secElapsed(mission_time);

  args["start"] = std::to_string(time);

  act += args["start"];

  act += ",";

  args["duration"] = "1";

  act += "1,)";

  j_node n;
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = time;
  n.endtime = time;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = args["area_marked"];
  n.action.start = args["start"];
  n.action.duration = args["duration"];
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
  n.j["task"] = act;
  TeamSARState newstate = apply_operator(action,state,domain,args);
  n.new_s = newstate;
  n.starttime = 900;
  n.endtime = 900;
  n.action.action = action;
  n.action.agent = args["agent"];
  n.action.area = "NONE";
  n.action.start = args["start"];
  n.action.duration = args["duration"];
  return n;
}

// Generate specific trace size from start
parse_data team_sar_parser(std::string infile,
                     TeamSARState state,
                     TeamSARDomain& domain,
                     int trace_size = -1,
                     bool gen_file = false,
                     std::string outfile = "parsed_plan_trace.json") {
  std::string msg;

  std::ifstream rfile(infile);
  json j;
  std::unordered_map<std::string,int> regTriageTime;
  std::unordered_map<std::string,int> critTriageTime;
  std::unordered_map<int,int> c_awake;
  std::unordered_map<int,std::string> c_awake_area;
  parse_data p;
  int i = 0;
  p.initial_state = state;
  std::string player_key = "playername";
  std::unordered_map<std::string, Action> prevAct;
//  std::unordered_map<std::string,int> prev_act_endtime;
  while(getline(rfile,msg)) {
    if (i == trace_size) {
      break;
    }
    json g;
    g = json::parse(msg);

    if (g["topic"] == "trial" && g["msg"]["sub_type"] == "start") {
      if (g["data"]["client_info"][0].find("playername") == g["data"]["client_info"][0].end()) {
        player_key = "participant_id";
      }
      for (auto a : g["data"]["client_info"]) {
        state.agents.push_back(a[player_key].get<std::string>());
        state.agent_loc[a[player_key].get<std::string>()] = state.change_zone;
        regTriageTime[a[player_key].get<std::string>()] = 0;
        critTriageTime[a[player_key].get<std::string>()] = 0;
        state.holding[a[player_key].get<std::string>()] = false;
        state.time[a[player_key].get<std::string>()] = 0;
        state.loc_tracker[a[player_key].get<std::string>()] = {};
        state.action_tracker[a[player_key].get<std::string>()] = {};
        state.visited[a[player_key].get<std::string>()][state.change_zone] = 1;
        state.role[a[player_key].get<std::string>()] = "NONE";

        p.initial_state = state;
//        prev_act_endtime[a[player_key].get<std::string>()] = -1;
      }
    }
    if (g["data"]["mission_timer"] == "Mission Timer not initialized.") {
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        state.role[g["data"][player_key].get<std::string>()] = g["data"]["new_role"].get<std::string>();
        p.initial_state = state;
      }

    }
    if (g["data"]["mission_timer"] != "Mission Timer not initialized.") {
      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"][player_key] == state.agents[0]) {
        if (g["data"]["locations"][0]["id"] != state.agent_loc[state.agents[0]]) {
          j_node n = process_move_act(g,player_key,state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
          j[state.agents[0]].push_back(n.j);
          state = n.new_s;
          p.loc_tracker[state.agents[0]].push_back(state.agent_loc[state.agents[0]]);
          prevAct[state.agents[0]] = n.action;
          p.action_tracker[state.agents[0]].push_back(n.action); 
          i++;
//            prev_act_endtime[agents[0]] = n.endtime;
        }
      }

      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"][player_key] == state.agents[1]) {
        if (g["data"]["locations"][0]["id"] != state.agent_loc[state.agents[1]]) {
          j_node n = process_move_act(g,player_key,state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
          j[state.agents[1]].push_back(n.j);
          state = n.new_s;
          p.loc_tracker[state.agents[1]].push_back(state.agent_loc[state.agents[1]]);
          prevAct[state.agents[1]] = n.action;
          p.action_tracker[state.agents[1]].push_back(n.action);
          i++;
//            prev_act_endtime[agents[1]] = n.endtime;
        }
      }

      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"][player_key] == state.agents[2]) {
        if (g["data"]["locations"][0]["id"] != state.agent_loc[state.agents[2]]) {
          j_node n = process_move_act(g,player_key,state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
          j[state.agents[2]].push_back(n.j);
          state = n.new_s;
          p.loc_tracker[state.agents[2]].push_back(state.agent_loc[state.agents[2]]);
          prevAct[state.agents[2]] = n.action;
          p.action_tracker[state.agents[2]].push_back(n.action);
          i++;
//            prev_act_endtime[agents[2]] = n.endtime;
        }
      }
 
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        j_node n = process_change_role_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        j[player].push_back(n.j);
        state = n.new_s;
        prevAct[player] = n.action;
        p.action_tracker[player].push_back(n.action);
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"][player_key] == state.agents[0]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[state.agents[0]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageReg_act(g,player_key,regTriageTime[state.agents[0]],state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            j[state.agents[0]].push_back(n.j);
            state = n.new_s;
            prevAct[state.agents[0]] = n.action;
            p.action_tracker[state.agents[0]].push_back(n.action);
            i++;
//            prev_act_endtime[agents[0]] = n.endtime;
          }
          regTriageTime[state.agents[0]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"][player_key] == state.agents[1]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[state.agents[1]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageReg_act(g,player_key,regTriageTime[state.agents[1]],state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            j[state.agents[1]].push_back(n.j);
            state = n.new_s;
            prevAct[state.agents[1]] = n.action;
            p.action_tracker[state.agents[1]].push_back(n.action);
            i++;
//            prev_act_endtime[agents[1]] = n.endtime;
          }
          regTriageTime[state.agents[1]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"][player_key] == state.agents[2]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[state.agents[2]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageReg_act(g,player_key,regTriageTime[state.agents[2]],state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            j[state.agents[2]].push_back(n.j);
            state = n.new_s;
            prevAct[state.agents[2]] = n.action;
            p.action_tracker[state.agents[2]].push_back(n.action);
            i++;
//            prev_act_endtime[agents[2]] = n.endtime;
          }
          regTriageTime[state.agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"][player_key] == state.agents[0]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[state.agents[0]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageCrit_act(g,player_key,critTriageTime[state.agents[0]],state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            j[state.agents[0]].push_back(n.j);
            state = n.new_s;
            prevAct[state.agents[0]] = n.action;
            p.action_tracker[state.agents[0]].push_back(n.action);
            i++;
//            prev_act_endtime[agents[0]] = n.endtime;
          }
          critTriageTime[state.agents[0]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"][player_key] == state.agents[1]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[state.agents[1]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageCrit_act(g,player_key,critTriageTime[state.agents[1]],state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            j[state.agents[1]].push_back(n.j);
            state = n.new_s;
            prevAct[state.agents[1]] = n.action;
            p.action_tracker[state.agents[1]].push_back(n.action);
            i++;
//            prev_act_endtime[agents[1]] = n.endtime;
          }
          critTriageTime[state.agents[1]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"][player_key] == state.agents[2]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[state.agents[2]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageCrit_act(g,player_key,critTriageTime[state.agents[2]],state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            j[state.agents[2]].push_back(n.j);
            state = n.new_s;
            prevAct[state.agents[2]] = n.action;
            p.action_tracker[state.agents[2]].push_back(n.action);
            i++;
//            prev_act_endtime[agents[2]] = n.endtime;
          }
          critTriageTime[state.agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:ProximityBlockInteraction" &&
           g["data"]["players_in_range"] == 3 &&
           g["data"]["action_type"] == "ENTERED_RANGE") {
        j_node n = process_wakeCrit_act(g,state,domain);
        c_awake[g["data"]["victim_id"].get<int>()] = i;
        c_awake_area[g["data"]["victim_id"].get<int>()] = n.action.area;
//        for (auto a : agents) {
//          if (prev_act_endtime[a] != -1) {
//            if (n.starttime > prev_act_endtime[a]) {
//              j.push_back(add_search_act(a,c_loc[a],prev_act_endtime[a],n.starttime));
//            }
//          }
//          prev_act_endtime[a] = n.endtime;
//        }
        state = n.new_s;
        for (auto a : state.agents) {
          j[a].push_back(n.j);
          prevAct[a] = n.action;
          p.action_tracker[a].push_back(n.action);
        }
        i++;
      }  

      if (g["msg"]["sub_type"] == "Event:ProximityBlockInteraction" &&
          g["data"]["action_type"] == "LEFT_RANGE") {
        int vic = g["data"]["victim_id"].get<int>();
        if (c_awake.find(vic) != c_awake.end()) {
          state.c_awake[c_awake_area[vic]] = false;
          for (auto a : state.agents) {    
            j[a].erase(c_awake[vic]);
            p.action_tracker[a].erase(p.action_tracker[a].begin()+i);
          }
          i--;
        }
      }

      if (g["msg"]["sub_type"] == "Event:VictimPickedUp") {
        j_node n = process_pickUpVic_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        j[player].push_back(n.j);
        state = n.new_s;
        prevAct[player] = n.action;
        p.action_tracker[player].push_back(n.action);
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:VictimPlaced") {
        j_node n = process_putDownVic_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        j[player].push_back(n.j);
        state = n.new_s;
        prevAct[player] = n.action;
        p.action_tracker[player].push_back(n.action);
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:RubbleDestroyed") {
        j_node n = process_breakBlock_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        j[player].push_back(n.j);
        state = n.new_s;
        prevAct[player] = n.action;
        p.action_tracker[player].push_back(n.action);
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

//      if (g["msg"]["sub_type"] == "Event:MarkerPlaced") {
//        j_node n;
//        if (prevAct.find(g["data"][player_key].get<std::string>()) != prevAct.end()) {
//          Action act = prevAct[g["data"][player_key].get<std::string>()];
//          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
//          int time = missionTime2secElapsed(mission_time);
//          auto start = std::stoi(act.start,nullptr);
//          if (act.action == "!move" && (time - start) <= 10) {
//            n = process_markOpening_act(g,player_key,act.area,state,domain);
//          }
//          else {
//            n = process_markArea_act(g,player_key,state,domain);
//          }
//        }
//        else {
//          n = process_markArea_act(g,player_key,state,domain);
//        }
//        j.push_back(n.j);
//        state = n.new_s;
//        prevAct[g["data"][player_key].get<std::string>()] = n.action;
//        a_tracker.push_back(n.action);
//        i++;
//      }
    }
  }
  for (auto a : state.agents) {
    if (trace_size <= -1) {
      j_node n = add_exit(a,state,domain);

      j[a].push_back(n.j);
      state = n.new_s;
      p.action_tracker[a].push_back(n.action);
    }
    std::reverse(p.action_tracker[a].begin(),p.action_tracker[a].end());
    std::reverse(p.loc_tracker[a].begin(),p.loc_tracker[a].end());
  }
  p.trace = j;
  rfile.close();
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << j << std::endl;
  }

  return p;
}

// Generates segment given starting and ending point
parse_data team_sar_parser(std::string infile,
                     TeamSARState state,
                     TeamSARDomain& domain,
                     std::pair<int,int> trace_segment,
                     bool gen_file = false,
                     std::string outfile = "parsed_plan_trace.json") {
  std::string msg;

  std::ifstream rfile(infile);
  json j;
  std::unordered_map<std::string,int> regTriageTime;
  std::unordered_map<std::string,int> critTriageTime;
  std::unordered_map<int,int> c_awake;
  std::unordered_map<int,std::string> c_awake_area;
  parse_data p;
  int i = 0;
  p.initial_state = state;
  bool initial_set = false;
  std::string player_key = "playername";
  std::unordered_map<std::string, Action> prevAct;
//  std::unordered_map<std::string,int> prev_act_endtime;
  while(getline(rfile,msg)) {
    json g;
    g = json::parse(msg);

    if (g["topic"] == "trial" && g["msg"]["sub_type"] == "start") {
      if (g["data"]["client_info"][0].find("playername") == g["data"]["client_info"][0].end()) {
        player_key = "participant_id";
      }
      for (auto a : g["data"]["client_info"]) {
        state.agents.push_back(a[player_key].get<std::string>());
        state.agent_loc[a[player_key].get<std::string>()] = state.change_zone;
        regTriageTime[a[player_key].get<std::string>()] = 0;
        critTriageTime[a[player_key].get<std::string>()] = 0;
        state.holding[a[player_key].get<std::string>()] = false;
        state.time[a[player_key].get<std::string>()] = 0;
        state.loc_tracker[a[player_key].get<std::string>()] = {};
        state.action_tracker[a[player_key].get<std::string>()] = {};
        state.visited[a[player_key].get<std::string>()][state.change_zone] = 1;
        state.role[a[player_key].get<std::string>()] = "NONE";

        p.initial_state = state;
//        prev_act_endtime[a[player_key].get<std::string>()] = -1;
      }
    }
    if (!state.agents.empty()) {
      int min_time = std::min({state.time[state.agents[0]],state.time[state.agents[1]], state.time[state.agents[2]]});
      if (min_time >= trace_segment.second) {
        break;
      }
    }
    if (g["data"]["mission_timer"] == "Mission Timer not initialized.") {
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        state.role[g["data"][player_key].get<std::string>()] = g["data"]["new_role"].get<std::string>();
        p.initial_state = state;
      }

    }
    if (g["data"]["mission_timer"] != "Mission Timer not initialized.") {
      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"][player_key] == state.agents[0]) {
        if (g["data"]["locations"][0]["id"] != state.agent_loc[state.agents[0]]) {
          j_node n = process_move_act(g,player_key,state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
          if (state.time[state.agents[0]] >= trace_segment.first &&
              state.time[state.agents[0]] <= trace_segment.second) {
            if (!initial_set) {
              p.initial_state = state;
              initial_set = true;
            }
            j[state.agents[0]].push_back(n.j);
            p.loc_tracker[state.agents[0]].push_back(state.agent_loc[state.agents[0]]);
            p.action_tracker[state.agents[0]].push_back(n.action); 
          }
          state = n.new_s;
          prevAct[state.agents[0]] = n.action;
          i++;
//            prev_act_endtime[agents[0]] = n.endtime;
        }
      }

      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"][player_key] == state.agents[1]) {
        if (g["data"]["locations"][0]["id"] != state.agent_loc[state.agents[1]]) {
          j_node n = process_move_act(g,player_key,state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
          if (state.time[state.agents[1]] >= trace_segment.first &&
              state.time[state.agents[1]] <= trace_segment.second) {
            if (!initial_set) {
              p.initial_state = state;
              initial_set = true;
            }
            j[state.agents[1]].push_back(n.j);
            p.loc_tracker[state.agents[1]].push_back(state.agent_loc[state.agents[1]]);
            p.action_tracker[state.agents[1]].push_back(n.action); 
          }
          state = n.new_s;
          prevAct[state.agents[1]] = n.action;
          i++;
//            prev_act_endtime[agents[1]] = n.endtime;
        }
      }

      if (g["msg"]["sub_type"] == "Event:location" && 
          g["data"].contains("locations") &&
          g["data"][player_key] == state.agents[2]) {
        if (g["data"]["locations"][0]["id"] != state.agent_loc[state.agents[2]]) {
          j_node n = process_move_act(g,player_key,state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
          if (state.time[state.agents[2]] >= trace_segment.first &&
              state.time[state.agents[2]] <= trace_segment.second) {
            if (!initial_set) {
              p.initial_state = state;
              initial_set = true;
            }
            j[state.agents[2]].push_back(n.j);
            p.loc_tracker[state.agents[2]].push_back(state.agent_loc[state.agents[2]]);
            p.action_tracker[state.agents[2]].push_back(n.action); 
          }
          state = n.new_s;
          prevAct[state.agents[2]] = n.action;
          i++;
//            prev_act_endtime[agents[2]] = n.endtime;
        }
      }
 
      if (g["msg"]["sub_type"] == "Event:RoleSelected") {
        j_node n = process_change_role_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        if (state.time[player] >= trace_segment.first &&
            state.time[player] <= trace_segment.second) {
          if (!initial_set) {
            p.initial_state = state;
            initial_set = true;
          }
          j[player].push_back(n.j);
          p.action_tracker[player].push_back(n.action); 
        }
        state = n.new_s;
        prevAct[player] = n.action;
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"][player_key] == state.agents[0]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[state.agents[0]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageReg_act(g,player_key,regTriageTime[state.agents[0]],state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            if (state.time[state.agents[0]] >= trace_segment.first &&
              state.time[state.agents[0]] <= trace_segment.second) {
              if (!initial_set) {
                p.initial_state = state;
                initial_set = true;
              }
              j[state.agents[0]].push_back(n.j);
              p.action_tracker[state.agents[0]].push_back(n.action); 
            }
            state = n.new_s;
            prevAct[state.agents[0]] = n.action;
            i++;
//            prev_act_endtime[agents[0]] = n.endtime;
          }
          regTriageTime[state.agents[0]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"][player_key] == state.agents[1]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[state.agents[1]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageReg_act(g,player_key,regTriageTime[state.agents[1]],state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            if (state.time[state.agents[1]] >= trace_segment.first &&
              state.time[state.agents[1]] <= trace_segment.second) {
              if (!initial_set) {
                p.initial_state = state;
                initial_set = true;
              }
              j[state.agents[1]].push_back(n.j);
              p.action_tracker[state.agents[1]].push_back(n.action); 
            }
            state = n.new_s;
            prevAct[state.agents[1]] = n.action;
            i++;
//            prev_act_endtime[agents[1]] = n.endtime;
          }
          regTriageTime[state.agents[1]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "REGULAR" &&
          g["data"][player_key] == state.agents[2]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          regTriageTime[state.agents[2]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageReg_act(g,player_key,regTriageTime[state.agents[2]],state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            if (state.time[state.agents[2]] >= trace_segment.first &&
              state.time[state.agents[2]] <= trace_segment.second) {
              if (!initial_set) {
                p.initial_state = state;
                initial_set = true;
              }
              j[state.agents[2]].push_back(n.j);
              p.action_tracker[state.agents[2]].push_back(n.action); 
            }
            state = n.new_s;
            prevAct[state.agents[2]] = n.action;
            i++;
//            prev_act_endtime[agents[2]] = n.endtime;
          }
          regTriageTime[state.agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"][player_key] == state.agents[0]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[state.agents[0]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageCrit_act(g,player_key,critTriageTime[state.agents[0]],state,domain);
//            if (prev_act_endtime[agents[0]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[0]]) {
//                j.push_back(add_search_act(agents[0],
//                                           c_loc[agents[0]],
//                                           prev_act_endtime[agents[0]],
//                                           n.starttime));
//              }
//            }
            if (state.time[state.agents[0]] >= trace_segment.first &&
              state.time[state.agents[0]] <= trace_segment.second) {
              if (!initial_set) {
                p.initial_state = state;
                initial_set = true;
              }
              j[state.agents[0]].push_back(n.j);
              p.action_tracker[state.agents[0]].push_back(n.action); 
            }
            state = n.new_s;
            prevAct[state.agents[0]] = n.action;
            i++;
//            prev_act_endtime[agents[0]] = n.endtime;
          }
          critTriageTime[state.agents[0]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"][player_key] == state.agents[1]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[state.agents[1]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageCrit_act(g,player_key,critTriageTime[state.agents[1]],state,domain);
//            if (prev_act_endtime[agents[1]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[1]]) {
//                j.push_back(add_search_act(agents[1],
//                                           c_loc[agents[1]],
//                                           prev_act_endtime[agents[1]],
//                                           n.starttime));
//              }
//            }
            if (state.time[state.agents[1]] >= trace_segment.first &&
              state.time[state.agents[1]] <= trace_segment.second) {
              if (!initial_set) {
                p.initial_state = state;
                initial_set = true;
              }
              j[state.agents[1]].push_back(n.j);
              p.action_tracker[state.agents[1]].push_back(n.action); 
            }
            state = n.new_s;
            prevAct[state.agents[1]] = n.action;
            i++;
//            prev_act_endtime[agents[1]] = n.endtime;
          }
          critTriageTime[state.agents[1]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:Triage" && 
          g["data"]["type"] == "CRITICAL" &&
          g["data"][player_key] == state.agents[2]) {
        if (g["data"]["triage_state"] == "IN_PROGRESS") {
          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
          critTriageTime[state.agents[2]] = missionTime2secElapsed(mission_time);
        }
        else {
          if (g["data"]["triage_state"] == "SUCCESSFUL") {
            j_node n = process_triageCrit_act(g,player_key,critTriageTime[state.agents[2]],state,domain);
//            if (prev_act_endtime[agents[2]] != -1) {
//              if (n.starttime > prev_act_endtime[agents[2]]) {
//                j.push_back(add_search_act(agents[2],
//                                           c_loc[agents[2]],
//                                           prev_act_endtime[agents[2]],
//                                           n.starttime));
//              }
//            }
            if (state.time[state.agents[2]] >= trace_segment.first &&
              state.time[state.agents[2]] <= trace_segment.second) {
              if (!initial_set) {
                p.initial_state = state;
                initial_set = true;
              }
              j[state.agents[2]].push_back(n.j);
              p.action_tracker[state.agents[2]].push_back(n.action); 
            }
            state = n.new_s;
            prevAct[state.agents[2]] = n.action;
            i++;
//            prev_act_endtime[agents[2]] = n.endtime;
          }
          critTriageTime[state.agents[2]] = 0;
        }
      }

      if (g["msg"]["sub_type"] == "Event:ProximityBlockInteraction" &&
           g["data"]["players_in_range"] == 3 &&
           g["data"]["action_type"] == "ENTERED_RANGE") {
        j_node n = process_wakeCrit_act(g,state,domain);
        c_awake_area[g["data"]["victim_id"].get<int>()] = n.action.area;
        c_awake[g["data"]["victim_id"].get<int>()] = i;
//        for (auto a : agents) {
//          if (prev_act_endtime[a] != -1) {
//            if (n.starttime > prev_act_endtime[a]) {
//              j.push_back(add_search_act(a,c_loc[a],prev_act_endtime[a],n.starttime));
//            }
//          }
//          prev_act_endtime[a] = n.endtime;
//        }
        bool record = false;
        if (state.time[state.agents[0]] >= trace_segment.first &&
            state.time[state.agents[0]] <= trace_segment.second) {
          if (!initial_set) {
            p.initial_state = state;
            initial_set = true;
          }
          record = true;
        }
        state = n.new_s;
        for (auto a : state.agents) {
          if (record) {
            j[a].push_back(n.j);
            p.action_tracker[a].push_back(n.action); 
          }
          prevAct[a] = n.action;
        }
        i++;
      }  

      if (g["msg"]["sub_type"] == "Event:ProximityBlockInteraction" &&
          g["data"]["action_type"] == "LEFT_RANGE") {
        int vic = g["data"]["victim_id"].get<int>();
        if (c_awake.find(vic) != c_awake.end()) {
          state.c_awake[c_awake_area[vic]] = false;
          p.initial_state.c_awake[c_awake_area[vic]] = false;
          for (auto a : state.agents) {
            j[a].erase(c_awake[vic]);
            p.action_tracker[a].erase(p.action_tracker[a].begin()+i);
          }
          i--;
        }
      }

      if (g["msg"]["sub_type"] == "Event:VictimPickedUp") {
        j_node n = process_pickUpVic_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        if (state.time[player] >= trace_segment.first &&
            state.time[player] <= trace_segment.second) {
          if (!initial_set) {
            p.initial_state = state;
            initial_set = true;
          }
          j[player].push_back(n.j);
          p.action_tracker[player].push_back(n.action); 
        }
        state = n.new_s;
        prevAct[player] = n.action;
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:VictimPlaced") {
        j_node n = process_putDownVic_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        if (state.time[player] >= trace_segment.first &&
            state.time[player] <= trace_segment.second) {
          if (!initial_set) {
            p.initial_state = state;
            initial_set = true;
          }
          j[player].push_back(n.j);
          p.action_tracker[player].push_back(n.action); 
        }
        state = n.new_s;
        prevAct[player] = n.action;
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

      if (g["msg"]["sub_type"] == "Event:RubbleDestroyed") {
        j_node n = process_breakBlock_act(g,player_key,state,domain);
//        if (prev_act_endtime[p] != -1) {
//          if (n.starttime > prev_act_endtime[p]) {
//            j.push_back(add_search_act(p,c_loc[p],prev_act_endtime[p],n.starttime));
//          }
//        }
        std::string player = g["data"][player_key].get<std::string>();
        if (state.time[player] >= trace_segment.first &&
            state.time[player] <= trace_segment.second) {
          if (!initial_set) {
            p.initial_state = state;
            initial_set = true;
          }
          j[player].push_back(n.j);
          p.action_tracker[player].push_back(n.action); 
        }
        state = n.new_s;
        prevAct[player] = n.action;
        i++;
//        prev_act_endtime[p] = n.endtime;
      }

//      if (g["msg"]["sub_type"] == "Event:MarkerPlaced") {
//        j_node n;
//        if (prevAct.find(g["data"][player_key].get<std::string>()) != prevAct.end()) {
//          Action act = prevAct[g["data"][player_key].get<std::string>()];
//          std::string mission_time = g["data"]["mission_timer"].get<std::string>();
//          int time = missionTime2secElapsed(mission_time);
//          auto start = std::stoi(act.start,nullptr);
//          if (act.action == "!move" && (time - start) <= 10) {
//            n = process_markOpening_act(g,player_key,act.area,state,domain);
//          }
//          else {
//            n = process_markArea_act(g,player_key,state,domain);
//          }
//        }
//        else {
//          n = process_markArea_act(g,player_key,state,domain);
//        }
//        j.push_back(n.j);
//        state = n.new_s;
//        prevAct[g["data"][player_key].get<std::string>()] = n.action;
//        a_tracker.push_back(n.action);
//        i++;
//      }
    }
  }
  for (auto a : state.agents) {
    if (trace_segment.second >= 900) {
      j_node n = add_exit(a,state,domain);

      j[a].push_back(n.j);
      state = n.new_s;
      p.action_tracker[a].push_back(n.action);
    } 
    std::reverse(p.action_tracker[a].begin(),p.action_tracker[a].end());
    std::reverse(p.loc_tracker[a].begin(),p.loc_tracker[a].end());
  }
  p.trace = j;
  rfile.close();
  if (gen_file) {
    std::ofstream o(outfile);
    o << std::setw(4) << j << std::endl;
  }

  return p;
}
