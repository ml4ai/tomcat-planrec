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

vector<std::string> split(std::string str) {
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
          this->start = true;
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/location") {
      try {
        json::error_code ec;
        jv.find_pointer("/data/locations",ec);
        if (!ec) {
          auto player_color = jv.at_pointer("/data/callsign").as_string();
          std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
          auto loc = jv.at_pointer("/data/locations/0/id").as_string();
          time = time.substr(time.find("T") + 1);
          time = time.substr(0,time.find("Z"));
          Time msg_time(time);
          if (player_color == "Red") {
            if (this->medic_current_loc != loc) {
              std::pair<std::string,std::string> act;
              std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
              act.first = "location";
              act.second = "(location medic " + this->medic_current_loc + " " + loc.c_str() +")"; 
              this->medic_current_loc = loc.c_str();
              std::string rank = elapsed_ms + "-*";
              this->rc->redis.xadd("actions",rank,{act});
            }
          }
          else if (player_color == "Blue") {
            if (this->engineer_current_loc != loc) {
              std::pair<std::string,std::string> act;
              std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
              act.first = "location";
              act.second = "(location engineer " + this->engineer_current_loc + " " + loc.c_str() +")"; 
              this->engineer_current_loc = loc.c_str();
              std::string rank = elapsed_ms + "-*";
              this->rc->redis.xadd("actions",rank,{act});
            }
          }
          else {
            if (this->transporter_current_loc != loc) {
              std::pair<std::string,std::string> act;
              std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
              act.first = "location";
              act.second = "(location transporter " + this->transporter_current_loc + " " + loc.c_str() +")"; 
              this->transporter_current_loc = loc.c_str();
              std::string rank = elapsed_ms + "-*";
              this->rc->redis.xadd("actions",rank,{act});
            }
          }
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/victim_placed") {
      try {
        auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        if (player_color == "RED") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "place_victim";
          act.second = "(place_victim medic vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->medic_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else if (player_color == "BLUE") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "place_victim";
          act.second = "(place_victim engineer vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->engineer_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "place_victim";
          act.second = "(place_victim transporter vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->transporter_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/victim_picked_up") {
      try {
        auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        if (player_color == "RED") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "pickup_victim";
          act.second = "(pickup_victim medic vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->medic_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else if (player_color == "BLUE") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "pickup_victim";
          act.second = "(pickup_victim engineer vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->engineer_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "pickup_victim";
          act.second = "(pickup_victim transporter vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->transporter_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/triage") {
      try {
        if (jv.at_pointer("/data/triage_state").as_string() == "SUCCESSFUL") {
          std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
          time = time.substr(time.find("T") + 1);
          time = time.substr(0,time.find("Z"));
          Time msg_time(time);
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "triage_victim";
          act.second = "(triage_victim medic vic_" + 
            to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
            " " + this->medic_current_loc +")"; 
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/rubble_destroyed") {
      try {
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        std::pair<std::string,std::string> act;
        std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
        act.first = "rubble_destroyed";
        act.second = "(rubble_destroyed engineer " + this->engineer_current_loc +")"; 
        std::string rank = elapsed_ms + "-*";
        this->rc->redis.xadd("actions",rank,{act});
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/marker_placed") {
      try {
        auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        if (player_color == "RED") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "marker_placed";
          act.second = "(marker_placed medic " + 
            split(jv.at_pointer("/data/type").as_string().c_str()).at(1) + 
            " " + this->medic_current_loc + ")";
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else if (player_color == "BLUE") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "marker_placed";
          act.second = "(marker_placed engineer " + 
            split(jv.at_pointer("/data/type").as_string().c_str()).at(1) + 
            " " + this->engineer_current_loc + ")";
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "marker_placed";
          act.second = "(marker_placed transporter " + 
            split(jv.at_pointer("/data/type").as_string().c_str()).at(1) + 
            " " + this->transporter_current_loc + ")";
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/player/marker_removed") {
      try {
        auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        auto marker_type = split(jv.at_pointer("/data/type").as_string().c_str());
        std::string marker_placer = "";
        if (marker_type.at(0) == "red") {
          marker_placer = "medic";
        } 
        else if (marker_type.at(0) == "blue") {
          marker_placer = "engineer";
        }
        else {
          marker_placer = "transporter";
        }
        if (player_color == "RED") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "marker_removed";
          act.second = "(marker_removed medic " + 
            marker_type.at(1) + 
            " " +
            marker_placer +
            this->medic_current_loc + ")";
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else if (player_color == "BLUE") {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "marker_removed";
          act.second = "(marker_removed engineer " + 
            marker_type.at(1) + 
            " " +
            marker_placer +
            this->engineer_current_loc + ")";
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
        else {
          std::pair<std::string,std::string> act;
          std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
          act.first = "marker_removed";
          act.second = "(marker_removed transporter " + 
            marker_type.at(1) + 
            " " +
            marker_placer +
            this->transporter_current_loc + ")";
          std::string rank = elapsed_ms + "-*";
          this->rc->redis.xadd("actions",rank,{act});
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }

    if (msg->get_topic() == "observations/events/player/proximity_block") {
      try {
        auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
        std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        if (player_color == "RED") {
          if (jv.at_pointer("/data/awake").as_bool()) {
            std::pair<std::string,std::string> act;
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            int vic_id = int(jv.at_pointer("/data/victim_id").as_int64());
            std::string assistant = "";
            if (this->engineer_assist.contains(vic_id)) {
              assistant = "engineer";
              this->engineer_assist.erase(vic_id);
            }
            if (this->transporter_assist.erase(vic_id)) {
              assistant = "transporter";
              this->transporter_assist.erase(vic_id);
            }
            act.first = "wake_critical_victim";
            act.second = "(wake_critical_victim medic " +
              assistant + " " +
              "vic_" + to_string(vic_id) + 
              " " + this->medic_current_loc +")"; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("actions",rank,{act});
          }
        }
        else if (player_color == "BLUE") {
          int vic_id = int(jv.at_pointer("/data/victim_id").as_int64());
          if (jv.at_pointer("/data/awake").as_bool()) {
            std::pair<std::string,std::string> act;
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            act.first = "wake_critical_victim";
            act.second = "(wake_critical_victim medic engineer vic_" + 
              to_string(vic_id) + 
              " " + this->medic_current_loc +")"; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("actions",rank,{act});
          }
          else {
            if (jv.at_pointer("/data/action_type").as_string() == "ENTERED_RANGE" &&
                jv.at_pointer("/data/players_in_range").as_int64() < 3) {
              this->engineer_assist.insert(vic_id); 
            }
            else {
              if (this->engineer_assist.contains(vic_id)) {
                this->engineer_assist.erase(vic_id);
              }
            }
          }
        }
        else {
          int vic_id = int(jv.at_pointer("/data/victim_id").as_int64());
          if (jv.at_pointer("/data/awake").as_bool()) {
            std::pair<std::string,std::string> act;
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            act.first = "wake_critical_victim";
            act.second = "(wake_critical_victim medic transporter vic_" + 
              to_string(vic_id) + 
              " " + this->medic_current_loc +")"; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("actions",rank,{act});
          }
          else {
            if (jv.at_pointer("/data/action_type").as_string() == "ENTERED_RANGE" &&
                jv.at_pointer("/data/players_in_range").as_int64() < 3) {
              this->transporter_assist.insert(vic_id); 
            }
            else {
              if (this->transporter_assist.contains(vic_id)) {
                this->transporter_assist.erase(vic_id);
              }
            }
          }
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "observations/events/server/victim_evacuated") {
      try {
        if (jv.at_pointer("/data/success").as_bool()) {
          auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
          std::string time = jv.at_pointer("/msg/timestamp").as_string().c_str();
          time = time.substr(time.find("T") + 1);
          time = time.substr(0,time.find("Z"));
          Time msg_time(time);
          if (player_color == "RED") {
            std::pair<std::string,std::string> act;
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            act.first = "rescue_victim";
            act.second = "(rescue_victim medic vic_" + 
              to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
              " " + this->medic_current_loc +")"; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("actions",rank,{act});
          }
          else if (player_color == "BLUE") {
            std::pair<std::string,std::string> act;
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            act.first = "rescue_victim";
            act.second = "(rescue_victim engineer vic_" + 
              to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
              " " + this->engineer_current_loc +")"; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("actions",rank,{act});
          }
          else {
            std::pair<std::string,std::string> act;
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            act.first = "rescue_victim";
            act.second = "(rescue_victim transporter vic_" + 
              to_string(int(jv.at_pointer("/data/victim_id").as_int64())) + 
              " " + this->transporter_current_loc +")"; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("actions",rank,{act});
          }
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
    if (msg->get_topic() == "agent/pygl_fov/player/3d/summary") {
      try {
        auto player_color = split(jv.at_pointer("/data/playername").as_string().c_str()).at(0);
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
              percept.first = "fov_victim_regular";
              percept.second = "(fov_victim_regular medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "fov_victim_critical";
              percept.second = "(fov_victim_critical medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "fov_victim_saved";
              percept.second = "(fov_victim_saved medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos && !see_gravel) {
              percept.first = "fov_gravel";
              percept.second = "(fov_gravel medic)";
              see_gravel = true;
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
              if (v.at_pointer("/marker_type").as_string().find("blue_novictim") != std::string::npos && !see_blue_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic novictim engineer)";
                see_blue_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_novictim") != std::string::npos && !see_green_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic novictim transporter)";
                see_green_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_novictim") != std::string::npos && !see_red_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic novictim medic)";
                see_red_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_sos") != std::string::npos && !see_blue_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic sos engineer)";
                see_blue_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_sos") != std::string::npos && !see_green_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic sos transporter)";
                see_green_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_sos") != std::string::npos && !see_red_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic sos medic)";
                see_red_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_regularvictim") != std::string::npos && !see_blue_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic regularvictim engineer)";
                see_blue_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_regularvictim") != std::string::npos && !see_green_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic regularvictim transporter)";
                see_green_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_regularvictim") != std::string::npos && !see_red_regularvictim) {
                percept.first = "fov_marker ";
                percept.second = "(fov_marker medic regularvictim medic)";
                see_red_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_criticalvictim") != std::string::npos && !see_blue_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic criticalvictim engineer)";
                see_blue_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_criticalvictim") != std::string::npos && !see_green_criticalvictim) {
                percept.first = "fov_marker ";
                percept.second = "(fov_marker medic criticalvictim transporter)";
                see_green_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_criticalvictim") != std::string::npos && !see_red_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic criticalvictim medic)";
                see_red_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_abrasion") != std::string::npos && !see_blue_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic abrasion engineer)";
                see_blue_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_abrasion") != std::string::npos && !see_green_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic abrasion transporter)";
                see_green_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_abrasion") != std::string::npos && !see_red_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic abrasion medic)";
                see_red_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_bonedamage") != std::string::npos && !see_blue_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic bonedamage engineer)";
                see_blue_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_bonedamage") != std::string::npos && !see_green_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic bonedamage transporter)";
                see_green_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_bonedamage") != std::string::npos && !see_red_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic bonedamage medic)";
                see_red_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_rubble") != std::string::npos && !see_blue_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic rubble engineer)";
                see_blue_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_rubble") != std::string::npos && !see_green_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic rubble transporter)";
                see_green_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_rubble") != std::string::npos && !see_red_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic rubble medic)";
                see_red_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_threat") != std::string::npos && !see_blue_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic threat engineer)";
                see_blue_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_threat") != std::string::npos && !see_green_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic threat transporter)";
                see_green_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_threat") != std::string::npos && !see_red_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker medic threat medic)";
                see_red_threat = true;
                fov.push_back(percept);
              }
            }
          }
          if (!fov.empty()) {
            std::string elapsed_ms = time_diff(msg_time, this->initial_time); 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("fov",rank,fov.begin(),fov.end());
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
              percept.first = "fov_victim_regular";
              percept.second = "(fov_victim_regular engineer vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "fov_victim_critical";
              percept.second = "(fov_victim_critical engineer vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "fov_victim_saved";
              percept.second = "(fov_victim_saved engineer vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos && !see_gravel) {
              percept.first = "fov_gravel";
              percept.second = "(fov_gravel engineer)";
              see_gravel = true;
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
              if (v.at_pointer("/marker_type").as_string().find("blue_novictim") != std::string::npos && !see_blue_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer novictim engineer)";
                see_blue_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_novictim") != std::string::npos && !see_green_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer novictim transporter)";
                see_green_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_novictim") != std::string::npos && !see_red_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer novictim medic)";
                see_red_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_sos") != std::string::npos && !see_blue_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer sos engineer)";
                see_blue_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_sos") != std::string::npos && !see_green_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer sos transporter)";
                see_green_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_sos") != std::string::npos && !see_red_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer sos medic)";
                see_red_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_regularvictim") != std::string::npos && !see_blue_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer regularvictim engineer)";
                see_blue_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_regularvictim") != std::string::npos && !see_green_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer regularvictim transporter)";
                see_green_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_regularvictim") != std::string::npos && !see_red_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer regularvictim medic)";
                see_red_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_criticalvictim") != std::string::npos && !see_blue_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer criticalvictim engineer)";
                see_blue_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_criticalvictim") != std::string::npos && !see_green_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer criticalvictim transporter)";
                see_green_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_criticalvictim") != std::string::npos && !see_red_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer criticalvictim medic)";
                see_red_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_abrasion") != std::string::npos && !see_blue_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer abrasion engineer)";
                see_blue_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_abrasion") != std::string::npos && !see_green_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer abrasion transporter)";
                see_green_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_abrasion") != std::string::npos && !see_red_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer abrasion medic)";
                see_red_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_bonedamage") != std::string::npos && !see_blue_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer bonedamage engineer)";
                see_blue_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_bonedamage") != std::string::npos && !see_green_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer bonedamage transporter)";
                see_green_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_bonedamage") != std::string::npos && !see_red_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer bonedamage medic)";
                see_red_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_rubble") != std::string::npos && !see_blue_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer rubble engineer)";
                see_blue_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_rubble") != std::string::npos && !see_green_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer rubble transporter)";
                see_green_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_rubble") != std::string::npos && !see_red_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer rubble medic)";
                see_red_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_threat") != std::string::npos && !see_blue_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer threat engineer)";
                see_blue_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_threat") != std::string::npos && !see_green_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer threat transporter)";
                see_green_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_threat") != std::string::npos && !see_red_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker engineer threat medic)";
                see_red_threat = true;
                fov.push_back(percept);
              }
            }

          }
          if (!fov.empty()) {
            std::string elapsed_ms = time_diff(msg_time, this->initial_time);; 
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("fov",rank,fov.begin(),fov.end());
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
              percept.first = "fov_victim_regular";
              percept.second = "(fov_victim_regular transporter vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "fov_victim_critical";
              percept.second = "(fov_victim_critical transporter vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "fov_victim_saved";
              percept.second = "(fov_victim_saved transporter vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              fov.push_back(percept);
            }
            if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos && !see_gravel) {
              percept.first = "fov_gravel";
              percept.second = "(fov_gravel transporter)";
              see_gravel = true;
              fov.push_back(percept);
            }

            if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
              if (v.at_pointer("/marker_type").as_string().find("blue_novictim") != std::string::npos && !see_blue_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter novictim engineer)";
                see_blue_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_novictim") != std::string::npos && !see_green_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter novictim transporter)";
                see_green_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_novictim") != std::string::npos && !see_red_novictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter novictim medic)";
                see_red_novictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_sos") != std::string::npos && !see_blue_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter sos engineer)";
                see_blue_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_sos") != std::string::npos && !see_green_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter sos transporter)";
                see_green_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_sos") != std::string::npos && !see_red_sos) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter sos medic)";
                see_red_sos = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_regularvictim") != std::string::npos && !see_blue_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter regularvictim engineer)";
                see_blue_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_regularvictim") != std::string::npos && !see_green_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter regularvictim transporter)";
                see_green_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_regularvictim") != std::string::npos && !see_red_regularvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter regularvictim medic)";
                see_red_regularvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_criticalvictim") != std::string::npos && !see_blue_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter criticalvictim engineer)";
                see_blue_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_criticalvictim") != std::string::npos && !see_green_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter criticalvictim transporter)";
                see_green_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_criticalvictim") != std::string::npos && !see_red_criticalvictim) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter criticalvictim medic)";
                see_red_criticalvictim = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_abrasion") != std::string::npos && !see_blue_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter abrasion engineer)";
                see_blue_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_abrasion") != std::string::npos && !see_green_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter abrasion transporter)";
                see_green_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_abrasion") != std::string::npos && !see_red_abrasion) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter abrasion medic)";
                see_red_abrasion = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_bonedamage") != std::string::npos && !see_blue_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter bonedamage engineer)";
                see_blue_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_bonedamage") != std::string::npos && !see_green_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter bonedamage transporter)";
                see_green_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_bonedamage") != std::string::npos && !see_red_bonedamage) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter bonedamage medic)";
                see_red_bonedamage = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_rubble") != std::string::npos && !see_blue_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter rubble engineer)";
                see_blue_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_rubble") != std::string::npos && !see_green_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter rubble transporter)";
                see_green_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_rubble") != std::string::npos && !see_red_rubble) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter rubble medic)";
                see_red_rubble = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("blue_threat") != std::string::npos && !see_blue_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter threat engineer)";
                see_blue_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("green_threat") != std::string::npos && !see_green_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter threat transporter)";
                see_green_threat = true;
                fov.push_back(percept);
              }

              if (v.at_pointer("/marker_type").as_string().find("red_threat") != std::string::npos && !see_red_threat) {
                percept.first = "fov_marker";
                percept.second = "(fov_marker transporter threat medic)";
                see_red_threat = true;
                fov.push_back(percept);
              }
            }

          }
          if (!fov.empty()) {
            std::string elapsed_ms = time_diff(msg_time, this->initial_time);
            std::string rank = elapsed_ms + "-*";
            this->rc->redis.xadd("fov",rank,fov.begin(),fov.end());
          }
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
}

PercAgent::PercAgent(string address, string const& redis_address = "tcp://127.0.0.1:6379") : Agent(address) {
  this->rc = Redis_Connect::getInstance(redis_address);
}
