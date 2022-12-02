#include "PercAgent.hpp"
#include <boost/json.hpp>
#include "file.hpp"
#include <iostream>


using namespace std;
namespace json = boost::json;

const int FOV_STACK_SIZE = 4;

void pretty_print(std::ostream &os,
                  json::value const &jv,
                  std::string *indent = nullptr) {
    std::string indent_;
    if (!indent)
        indent = &indent_;
    switch (jv.kind()) {
        case json::kind::object: {
            os << "{\n";
            indent->append(4, ' ');
            auto const &obj = jv.get_object();
            if (!obj.empty()) {
                auto it = obj.begin();
                for (;;) {
                    os << *indent << json::serialize(it->key()) << " : ";
                    pretty_print(os, it->value(), indent);
                    if (++it == obj.end())
                        break;
                    os << ",\n";
                }
            }
            os << "\n";
            indent->resize(indent->size() - 4);
            os << *indent << "}";
            break;
        }

        case json::kind::array: {
            os << "[\n";
            indent->append(4, ' ');
            auto const &arr = jv.get_array();
            if (!arr.empty()) {
                auto it = arr.begin();
                for (;;) {
                    os << *indent;
                    pretty_print(os, *it, indent);
                    if (++it == arr.end())
                        break;
                    os << ",\n";
                }
            }
            os << "\n";
            indent->resize(indent->size() - 4);
            os << *indent << "]";
            break;
        }

        case json::kind::string: {
            os << json::serialize(jv.get_string());
            break;
        }

        case json::kind::uint64:
            os << jv.get_uint64();
            break;

        case json::kind::int64:
            os << jv.get_int64();
            break;

        case json::kind::double_:
            os << jv.get_double();
            break;

        case json::kind::bool_:
            if (jv.get_bool())
                os << "true";
            else
                os << "false";
            break;

        case json::kind::null:
            os << "null";
            break;
    }

    if (indent->empty())
        os << "\n";
}

vector<std::string> split_player_name(std::string str) {
    std::replace(str.begin(), str.end(), '_', ' '); // replace ':' by ' '

    vector<std::string> array;
    stringstream ss(str);
    std::string temp;
    while (ss >> temp)
        array.push_back(temp);
    return array;
}

std::string time_diff(Time t1, Time t2) {
  double diff_seconds = ((t1.hours - t2.hours) * 3600.0) + ((t1.minutes - t2.minutes) * 60.0) + (t1.seconds - t2.seconds);
  double diff_r_milliseconds = round(diff_seconds*1000);
  return to_string(int(diff_r_milliseconds));
}

void PercAgent::process(mqtt::const_message_ptr msg) {
    json::value jv = json::parse(msg->to_string()).as_object();
    if (msg->get_topic() == "observations/events/mission") {
      try {
        if (jv.at_pointer("/data/mission_state").as_string().find("Start") != std::string::npos) {
          std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
          time = time.substr(time.find("T") + 1); 
          time = time.substr(0,time.find("Z"));
          this->initial_time = Time(time);
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "agent/pygl_fov/player/3d/summary") {
      try {
        auto player_color = split_player_name(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        if (player_color == "RED") {
          std::vector<std::pair<std::string,std::string>> fov;
          bool see_gravel = false;
          bool see_blue_novictim = false;
          bool see_green_novictim = false;
          bool see_red_novictim = false;

          bool see_blue_sos = false;
          bool see_green_sos = false;
          bool see_red_sos = false;
          
          bool see_red_regularvictim = false;
          bool see_red_criticalvictim = false;
          bool see_red_abrasion = false;
          bool see_red_bonedamage = false;
          bool see_red_rubble = false;
          bool see_red_threat = false;

          bool see_green_regularvictim = false;
          bool see_green_criticalvictim = false;
          bool see_green_abrasion = false;
          bool see_green_bonedamage = false;
          bool see_green_rubble = false;
          bool see_green_threat = false;

          bool see_blue_regularvictim = false;
          bool see_blue_criticalvictim = false;
          bool see_blue_abrasion = false;
          bool see_blue_bonedamage = false;
          bool see_blue_rubble = false;
          bool see_blue_threat = false;
          for (auto v: jv.at_pointer("/data/blocks").as_array()) {
            std::pair<std::string,std::string> percept;
            if (v.at_pointer("/type").as_string().find("block_victim_regular") != std::string::npos) {
              percept.first = "victim_regular";
              percept.second = "(fov_victim_regular medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "victim_critical";
              percept.second = "(fov_victim_critical medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "victim_saved";
              percept.second = "(fov_victim_saved medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos && !see_gravel) {
              percept.first = "gravel";
              percept.second = "(fov_gravel medic)";
              see_gravel = true;
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
              if (v.at_pointer("/marker_type").as_string().find("blue_novictim") != std::string::npos && !see_blue_novictim) {
                percept.first = "engineer_novictim";
                percept.second = "(fov_marker_novictim medic engineer)";
                see_blue_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_novictim") != std::string::npos && !see_green_novictim) {
                percept.first = "transporter_novictim";
                percept.second = "(fov_marker_novictim medic transporter)";
                see_green_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_novictim") != std::string::npos && !see_red_novictim) {
                percept.first = "medic_novictim";
                percept.second = "(fov_marker_novictim medic medic)";
                see_red_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_sos") != std::string::npos && !see_blue_sos) {
                percept.first = "engineer_sos";
                percept.second = "(fov_marker_sos medic engineer)";
                see_blue_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_sos") != std::string::npos && !see_green_sos) {
                percept.first = "transporter_sos";
                percept.second = "(fov_marker_sos medic transporter)";
                see_green_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_sos") != std::string::npos && !see_red_sos) {
                percept.first = "medic_sos";
                percept.second = "(fov_marker_sos medic medic)";
                see_red_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_regularvictim") != std::string::npos && !see_blue_regularvictim) {
                percept.first = "engineer_regularvictim";
                percept.second = "(fov_marker_regularvictim medic engineer)";
                see_blue_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_regularvictim") != std::string::npos && !see_green_regularvictim) {
                percept.first = "transporter_regularvictim";
                percept.second = "(fov_marker_regularvictim medic transporter)";
                see_green_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_regularvictim") != std::string::npos && !see_red_regularvictim) {
                percept.first = "medic_regularvictim";
                percept.second = "(fov_marker_regularvictim medic medic)";
                see_red_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_criticalvictim") != std::string::npos && !see_blue_criticalvictim) {
                percept.first = "engineer_criticalvictim";
                percept.second = "(fov_marker_criticalvictim medic engineer)";
                see_blue_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_criticalvictim") != std::string::npos && !see_green_criticalvictim) {
                percept.first = "transporter_criticalvictim";
                percept.second = "(fov_marker_criticalvictim medic transporter)";
                see_green_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_criticalvictim") != std::string::npos && !see_red_criticalvictim) {
                percept.first = "medic_criticalvictim";
                percept.second = "(fov_marker_criticalvictim medic medic)";
                see_red_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_abrasion") != std::string::npos && !see_blue_abrasion) {
                percept.first = "engineer_abrasion";
                percept.second = "(fov_marker_abrasion medic engineer)";
                see_blue_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_abrasion") != std::string::npos && !see_green_abrasion) {
                percept.first = "transporter_abrasion";
                percept.second = "(fov_marker_abrasion medic transporter)";
                see_green_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_abrasion") != std::string::npos && !see_red_abrasion) {
                percept.first = "medic_abrasion";
                percept.second = "(fov_marker_abrasion medic medic)";
                see_red_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_bonedamage") != std::string::npos && !see_blue_bonedamage) {
                percept.first = "engineer_bonedamage";
                percept.second = "(fov_marker_bonedamage medic engineer)";
                see_blue_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_bonedamage") != std::string::npos && !see_green_bonedamage) {
                percept.first = "transporter_bonedamage";
                percept.second = "(fov_marker_bonedamage medic transporter)";
                see_green_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_bonedamage") != std::string::npos && !see_red_bonedamage) {
                percept.first = "medic_bonedamage";
                percept.second = "(fov_marker_bonedamage medic medic)";
                see_red_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_rubble") != std::string::npos && !see_blue_rubble) {
                percept.first = "engineer_rubble";
                percept.second = "(fov_marker_rubble medic engineer)";
                see_blue_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_rubble") != std::string::npos && !see_green_rubble) {
                percept.first = "transporter_rubble";
                percept.second = "(fov_marker_rubble medic transporter)";
                see_green_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_rubble") != std::string::npos && !see_red_rubble) {
                percept.first = "medic_rubble";
                percept.second = "(fov_marker_rubble medic medic)";
                see_red_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_threat") != std::string::npos && !see_blue_threat) {
                percept.first = "engineer_threat";
                percept.second = "(fov_marker_threat medic engineer)";
                see_blue_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_threat") != std::string::npos && !see_green_threat) {
                percept.first = "transporter_threat";
                percept.second = "(fov_marker_threat medic transporter)";
                see_green_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_threat") != std::string::npos && !see_red_threat) {
                percept.first = "medic_threat";
                percept.second = "(fov_marker_threat medic medic)";
                see_red_threat = true;
                fov.push_back(percept);
              }
            }
          }
          if (!fov.empty()) {
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            std::string rank = elapsed_ms + "-*";
            this->redis.xadd("medic_fov",rank,fov.begin(),fov.end());
          }
        }
        else if (player_color == "BLUE") {
          std::vector<std::pair<std::string,std::string>> fov;
          bool see_gravel = false;
          bool see_blue_novictim = false;
          bool see_green_novictim = false;
          bool see_red_novictim = false;

          bool see_blue_sos = false;
          bool see_green_sos = false;
          bool see_red_sos = false;
          
          bool see_red_regularvictim = false;
          bool see_red_criticalvictim = false;
          bool see_red_abrasion = false;
          bool see_red_bonedamage = false;
          bool see_red_rubble = false;
          bool see_red_threat = false;

          bool see_green_regularvictim = false;
          bool see_green_criticalvictim = false;
          bool see_green_abrasion = false;
          bool see_green_bonedamage = false;
          bool see_green_rubble = false;
          bool see_green_threat = false;

          bool see_blue_regularvictim = false;
          bool see_blue_criticalvictim = false;
          bool see_blue_abrasion = false;
          bool see_blue_bonedamage = false;
          bool see_blue_rubble = false;
          bool see_blue_threat = false;
          for (auto v: jv.at_pointer("/data/blocks").as_array()) {
            std::pair<std::string,std::string> percept;
            if (v.at_pointer("/type").as_string().find("block_victim_regular") != std::string::npos) {
              percept.first = "victim_regular";
              percept.second = "(fov_victim_regular engineer vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "victim_critical";
              percept.second = "(fov_victim_critical engineer vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "victim_saved";
              percept.second = "(fov_victim_saved engineer vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos && !see_gravel) {
              percept.first = "gravel";
              percept.second = "(fov_gravel engineer)";
              see_gravel = true;
            }

            if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
              if (v.at_pointer("/marker_type").as_string().find("blue_novictim") != std::string::npos && !see_blue_novictim) {
                percept.first = "engineer_novictim";
                percept.second = "(fov_marker_novictim engineer engineer)";
                see_blue_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_novictim") != std::string::npos && !see_green_novictim) {
                percept.first = "transporter_novictim";
                percept.second = "(fov_marker_novictim engineer transporter)";
                see_green_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_novictim") != std::string::npos && !see_red_novictim) {
                percept.first = "medic_novictim";
                percept.second = "(fov_marker_novictim engineer medic)";
                see_red_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_sos") != std::string::npos && !see_blue_sos) {
                percept.first = "engineer_sos";
                percept.second = "(fov_marker_sos engineer engineer)";
                see_blue_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_sos") != std::string::npos && !see_green_sos) {
                percept.first = "transporter_sos";
                percept.second = "(fov_marker_sos engineer transporter)";
                see_green_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_sos") != std::string::npos && !see_red_sos) {
                percept.first = "medic_sos";
                percept.second = "(fov_marker_sos engineer medic)";
                see_red_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_regularvictim") != std::string::npos && !see_blue_regularvictim) {
                percept.first = "engineer_regularvictim";
                percept.second = "(fov_marker_regularvictim engineer engineer)";
                see_blue_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_regularvictim") != std::string::npos && !see_green_regularvictim) {
                percept.first = "transporter_regularvictim";
                percept.second = "(fov_marker_regularvictim engineer transporter)";
                see_green_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_regularvictim") != std::string::npos && !see_red_regularvictim) {
                percept.first = "medic_regularvictim";
                percept.second = "(fov_marker_regularvictim engineer medic)";
                see_red_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_criticalvictim") != std::string::npos && !see_blue_criticalvictim) {
                percept.first = "engineer_criticalvictim";
                percept.second = "(fov_marker_criticalvictim engineer engineer)";
                see_blue_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_criticalvictim") != std::string::npos && !see_green_criticalvictim) {
                percept.first = "transporter_criticalvictim";
                percept.second = "(fov_marker_criticalvictim engineer transporter)";
                see_green_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_criticalvictim") != std::string::npos && !see_red_criticalvictim) {
                percept.first = "medic_criticalvictim";
                percept.second = "(fov_marker_criticalvictim engineer medic)";
                see_red_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_abrasion") != std::string::npos && !see_blue_abrasion) {
                percept.first = "engineer_abrasion";
                percept.second = "(fov_marker_abrasion engineer engineer)";
                see_blue_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_abrasion") != std::string::npos && !see_green_abrasion) {
                percept.first = "transporter_abrasion";
                percept.second = "(fov_marker_abrasion engineer transporter)";
                see_green_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_abrasion") != std::string::npos && !see_red_abrasion) {
                percept.first = "medic_abrasion";
                percept.second = "(fov_marker_abrasion engineer medic)";
                see_red_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_bonedamage") != std::string::npos && !see_blue_bonedamage) {
                percept.first = "engineer_bonedamage";
                percept.second = "(fov_marker_bonedamage engineer engineer)";
                see_blue_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_bonedamage") != std::string::npos && !see_green_bonedamage) {
                percept.first = "transporter_bonedamage";
                percept.second = "(fov_marker_bonedamage engineer transporter)";
                see_green_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_bonedamage") != std::string::npos && !see_red_bonedamage) {
                percept.first = "medic_bonedamage";
                percept.second = "(fov_marker_bonedamage engineer medic)";
                see_red_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_rubble") != std::string::npos && !see_blue_rubble) {
                percept.first = "engineer_rubble";
                percept.second = "(fov_marker_rubble engineer engineer)";
                see_blue_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_rubble") != std::string::npos && !see_green_rubble) {
                percept.first = "transporter_rubble";
                percept.second = "(fov_marker_rubble engineer transporter)";
                see_green_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_rubble") != std::string::npos && !see_red_rubble) {
                percept.first = "medic_rubble";
                percept.second = "(fov_marker_rubble engineer medic)";
                see_red_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_threat") != std::string::npos && !see_blue_threat) {
                percept.first = "engineer_threat";
                percept.second = "(fov_marker_threat engineer engineer)";
                see_blue_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_threat") != std::string::npos && !see_green_threat) {
                percept.first = "transporter_threat";
                percept.second = "(fov_marker_threat engineer transporter)";
                see_green_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_threat") != std::string::npos && !see_red_threat) {
                percept.first = "medic_threat";
                percept.second = "(fov_marker_threat engineer medic)";
                see_red_threat = true;
                fov.push_back(percept);
              }
            }

          }
          if (!fov.empty()) {
            std::string elapsed_ms = time_diff(msg_time, this->initial_time);; 
            std::string rank = elapsed_ms + "-*";
            this->redis.xadd("engineer_fov",rank,fov.begin(),fov.end());
          }
        }
        else {
          std::vector<std::pair<std::string,std::string>> fov;
          bool see_gravel = false;
          bool see_blue_novictim = false;
          bool see_green_novictim = false;
          bool see_red_novictim = false;

          bool see_blue_sos = false;
          bool see_green_sos = false;
          bool see_red_sos = false;
          
          bool see_red_regularvictim = false;
          bool see_red_criticalvictim = false;
          bool see_red_abrasion = false;
          bool see_red_bonedamage = false;
          bool see_red_rubble = false;
          bool see_red_threat = false;

          bool see_green_regularvictim = false;
          bool see_green_criticalvictim = false;
          bool see_green_abrasion = false;
          bool see_green_bonedamage = false;
          bool see_green_rubble = false;
          bool see_green_threat = false;

          bool see_blue_regularvictim = false;
          bool see_blue_criticalvictim = false;
          bool see_blue_abrasion = false;
          bool see_blue_bonedamage = false;
          bool see_blue_rubble = false;
          bool see_blue_threat = false;
          for (auto v: jv.at_pointer("/data/blocks").as_array()) {
            std::pair<std::string,std::string> percept;
            if (v.at_pointer("/type").as_string().find("block_victim_regular") != std::string::npos) {
              percept.first = "victim_regular";
              percept.second = "(fov_victim_regular transporter vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "victim_critical";
              percept.second = "(fov_victim_critical transporter vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "victim_saved";
              percept.second = "(fov_victim_saved transporter vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos && !see_gravel) {
              percept.first = "gravel";
              percept.second = "(fov_gravel transporter)";
              see_gravel = true;
            }

            if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
              if (v.at_pointer("/marker_type").as_string().find("blue_novictim") != std::string::npos && !see_blue_novictim) {
                percept.first = "engineer_novictim";
                percept.second = "(fov_marker_novictim transporter engineer)";
                see_blue_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_novictim") != std::string::npos && !see_green_novictim) {
                percept.first = "transporter_novictim";
                percept.second = "(fov_marker_novictim transporter transporter)";
                see_green_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_novictim") != std::string::npos && !see_red_novictim) {
                percept.first = "medic_novictim";
                percept.second = "(fov_marker_novictim transporter medic)";
                see_red_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_sos") != std::string::npos && !see_blue_sos) {
                percept.first = "engineer_sos";
                percept.second = "(fov_marker_sos transporter engineer)";
                see_blue_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_sos") != std::string::npos && !see_green_sos) {
                percept.first = "transporter_sos";
                percept.second = "(fov_marker_sos transporter transporter)";
                see_green_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_sos") != std::string::npos && !see_red_sos) {
                percept.first = "medic_sos";
                percept.second = "(fov_marker_sos transporter medic)";
                see_red_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_regularvictim") != std::string::npos && !see_blue_regularvictim) {
                percept.first = "engineer_regularvictim";
                percept.second = "(fov_marker_regularvictim transporter engineer)";
                see_blue_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_regularvictim") != std::string::npos && !see_green_regularvictim) {
                percept.first = "transporter_regularvictim";
                percept.second = "(fov_marker_regularvictim transporter transporter)";
                see_green_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_regularvictim") != std::string::npos && !see_red_regularvictim) {
                percept.first = "medic_regularvictim";
                percept.second = "(fov_marker_regularvictim transporter medic)";
                see_red_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_criticalvictim") != std::string::npos && !see_blue_criticalvictim) {
                percept.first = "engineer_criticalvictim";
                percept.second = "(fov_marker_criticalvictim transporter engineer)";
                see_blue_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_criticalvictim") != std::string::npos && !see_green_criticalvictim) {
                percept.first = "transporter_criticalvictim";
                percept.second = "(fov_marker_criticalvictim transporter transporter)";
                see_green_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_criticalvictim") != std::string::npos && !see_red_criticalvictim) {
                percept.first = "medic_criticalvictim";
                percept.second = "(fov_marker_criticalvictim transporter medic)";
                see_red_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_abrasion") != std::string::npos && !see_blue_abrasion) {
                percept.first = "engineer_abrasion";
                percept.second = "(fov_marker_abrasion transporter engineer)";
                see_blue_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_abrasion") != std::string::npos && !see_green_abrasion) {
                percept.first = "transporter_abrasion";
                percept.second = "(fov_marker_abrasion transporter transporter)";
                see_green_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_abrasion") != std::string::npos && !see_red_abrasion) {
                percept.first = "medic_abrasion";
                percept.second = "(fov_marker_abrasion transporter medic)";
                see_red_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_bonedamage") != std::string::npos && !see_blue_bonedamage) {
                percept.first = "engineer_bonedamage";
                percept.second = "(fov_marker_bonedamage transporter engineer)";
                see_blue_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_bonedamage") != std::string::npos && !see_green_bonedamage) {
                percept.first = "transporter_bonedamage";
                percept.second = "(fov_marker_bonedamage transporter transporter)";
                see_green_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_bonedamage") != std::string::npos && !see_red_bonedamage) {
                percept.first = "medic_bonedamage";
                percept.second = "(fov_marker_bonedamage transporter medic)";
                see_red_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_rubble") != std::string::npos && !see_blue_rubble) {
                percept.first = "engineer_rubble";
                percept.second = "(fov_marker_rubble transporter engineer)";
                see_blue_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_rubble") != std::string::npos && !see_green_rubble) {
                percept.first = "transporter_rubble";
                percept.second = "(fov_marker_rubble transporter transporter)";
                see_green_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_rubble") != std::string::npos && !see_red_rubble) {
                percept.first = "medic_rubble";
                percept.second = "(fov_marker_rubble transporter medic)";
                see_red_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_threat") != std::string::npos && !see_blue_threat) {
                percept.first = "engineer_threat";
                percept.second = "(fov_marker_threat transporter engineer)";
                see_blue_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_threat") != std::string::npos && !see_green_threat) {
                percept.first = "transporter_threat";
                percept.second = "(fov_marker_threat transporter transporter)";
                see_green_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_threat") != std::string::npos && !see_red_threat) {
                percept.first = "medic_threat";
                percept.second = "(fov_marker_threat transporter medic)";
                see_red_threat = true;
                fov.push_back(percept);
              }
            }

          }
          if (!fov.empty()) {
            std::string elapsed_ms = time_diff(msg_time, this->initial_time);
            std::string rank = elapsed_ms + "-*";
            this->redis.xadd("transporter_fov",rank,fov.begin(),fov.end());
          }
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
}

PercAgent::PercAgent(string address,
                     string redis_address = "tcp://127.0.0.1:6379") : Agent(address),redis(redis_address) {}
