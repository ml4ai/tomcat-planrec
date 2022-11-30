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

void PercAgent::process(mqtt::const_message_ptr msg) {
    json::value jv = json::parse(msg->to_string()).as_object();
    if (msg->get_topic() == "observations/events/mission") {
      try {
        if (jv.at_pointer("/data/mission_state").as_string().find("Start") != std::string::npos) {
          std::string time = jv.at_pointer("/msg/timestamp").as_string();
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
        std::string time = jv.at_pointer("/msg/timestamp").as_string();
        time = time.substr(time.find("T") + 1);
        time = time.substr(0,time.find("Z"));
        Time msg_time(time);
        if (player_color == "RED") {
          std::vector<std::pair<std::string,std::string>> fov;
          for (auto v: jv.at_pointer("/data/blocks").as_array()) {
            std::pair<std::string,std::string> percept;
            if (v.at_pointer("/type").as_string().find("block_victim_regular") != std::string::npos) {
              percept.first = "victim_regular";
              percept.second = "(fov_victim_regular medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";

            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
              percept.first = "victim_critical";
              percept.second = "(fov_victim_critical medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
              percept.first = "victim_saved";
              percept.second = "(fov_victim_saved medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
            }
          }
        }
        else if (player_color == "BLUE") {
          for (auto v: jv.at_pointer("/data/blocks").as_array()) {
            if (v.at_pointer("/type").as_string().find("block_victim_regular") != std::string::npos) {
            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
            }
          }
        }
        else {
          for (auto v: jv.at_pointer("/data/blocks").as_array()) {
            if (v.at_pointer("/type").as_string().find("block_victim_regular") != std::string::npos) {
            }
            if (v.at_pointer("/type").as_string().find("block_victim_proximity") != std::string::npos) {
            }
            if (v.at_pointer("/type").as_string().find("block_victim_saved") != std::string::npos) {
            }
          }
        }
        for (auto v: jv.at_pointer("/data/blocks").as_array()) {
          auto player_color = split_player_name(
                                jv.at_pointer("/data/playername").as_string().c_str())
                                .at(0);
          if (v.at_pointer("/type").as_string().find("victim") != std::string::npos) {
            if (player_color == "RED") {
              std::string m_string = "(fov_victim medic vic_" + to_string(int(v.at_pointer("/id").as_int64()))+")";
              this->redis.xadd("red_vic","*",{field,m_string});
            } else if (player_color == "BLUE") {

            } else {

            }
          } else if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos) {
            if (player_color == "RED") {
              this->fov_medic.push_back(-10);
            } else if (player_color == "BLUE") {
              this->fov_engineer.push_back(-10);
            } else {
              this->fov_transporter.push_back(-10);
            }
          } else if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
            if (player_color == "RED") {
              if (v.at_pointer("/marker_type").as_string().find("novictim") != std::string::npos) {
                            this->fov_medic.push_back(-101);
              } else if (v.at_pointer("/marker_type").as_string().find("regularvictim") != std::string::npos) {
                            this->fov_medic.push_back(-102);
              } else if (v.at_pointer("/marker_type").as_string().find("criticalvictim") != std::string::npos) {
                            this->fov_medic.push_back(-103);
              } else if (v.at_pointer("/marker_type").as_string().find("threat") != std::string::npos) {
                            this->fov_medic.push_back(-104);
              } else if (v.at_pointer("/marker_type").as_string().find("bonedamage") != std::string::npos) {
                            this->fov_medic.push_back(-105);
              }
            } else if (player_color == "BLUE") {
              if (v.at_pointer("/marker_type").as_string().find("novictim") != std::string::npos) {
                            this->fov_engineer.push_back(-101);
              } else if (v.at_pointer("/marker_type").as_string().find("regularvictim") != std::string::npos) {
                            this->fov_engineer.push_back(-102);
              } else if (v.at_pointer("/marker_type").as_string().find("criticalvictim") != std::string::npos) {
                            this->fov_engineer.push_back(-103);
              } else if (v.at_pointer("/marker_type").as_string().find("threat") != std::string::npos) {
                            this->fov_engineer.push_back(-104);
              } else if (v.at_pointer("/marker_type").as_string().find("bonedamage") != std::string::npos) {
                            this->fov_engineer.push_back(-105);
              }
            } else {
              if (v.at_pointer("/marker_type").as_string().find("novictim") != std::string::npos) {
                            this->fov_transporter.push_back(-101);
              } else if (v.at_pointer("/marker_type").as_string().find("regularvictim") != std::string::npos) {
                            this->fov_transporter.push_back(-102);
              } else if (v.at_pointer("/marker_type").as_string().find("criticalvictim") != std::string::npos) {
                            this->fov_transporter.push_back(-103);
              } else if (v.at_pointer("/marker_type").as_string().find("threat") != std::string::npos) {
                            this->fov_transporter.push_back(-104);
              } else if (v.at_pointer("/marker_type").as_string().find("bonedamage") != std::string::npos) {
                            this->fov_transporter.push_back(-105);
              }
            }
          } else {
            if (player_color == "RED") {
              this->fov_medic.push_back(-1);
            } else if (player_color == "BLUE") {
                        this->fov_engineer.push_back(-1);
            } else {
                        this->fov_transporter.push_back(-1);
            }
          }
        }
      }
      catch (exception &exc) {
        cout << exc.what() << endl;
      }
    }
}

PercAgent::PercAgent(string
                     address,string redis_address = "tcp://127.0.0.1:6379") : Agent(address),redis(redis_address) {
    auto const s = read_file("../metadata/Saturn_2.6_3D_sm_v1.0.json");
    json::object jv = json::parse(s).as_object();
    vector<string> location_ids;
    for (const auto &loc: jv.at("locations").as_array()) {
        location_ids.emplace_back(loc.at("id").as_string().c_str());
    }
    location_ids.emplace_back("UNKNOWN");
    //Adding types and objects to KB
    TypeTree typetree;
    Objects objects;
    std::string root = "__Object__";
    typetree.add_root(root);
    typetree.add_child("Location",root);
    for (auto const& l: location_ids) {
      objects[l] = "Location";
    }
    typetree.add_child("Player_Status",root); 
    objects["safe"] = "Player_Status";
    objects["trapped"] = "Player_Status";
    std::vector<std::string> vic_ids;
    for (int i = 1; i <= 35; i++) {
        vic_ids.push_back("vic_" + to_string(i));
    }
    typetree.add_child("Victim",root); 
    for (auto const& v: vic_ids) {
      objects[v] = "Victim";
    }
    typetree.add_child("Victim_Type",root); 
    objects["a"] = "Victim_Type";
    objects["b"] = "Victim_Type";
    objects["c"] = "Victim_Type";

    typetree.add_child("Victim_Status",root); 
    objects["unsaved"] = "Victim_Status";
    objects["saved"] = "Victim_Status";

    typetree.add_child("Marker_Type",root);
    objects["novictim"] = "Marker_Type";
    objects["regularvictim"] = "Marker_Type";
    objects["criticalvictim"] =  "Marker_Type";
    objects["threat"] = "Marker_Type";
    objects["bonedamage"] = "Marker_Type";

    typetree.add_child("Role",root); 
    objects["medic"] = "Role";
    objects["transporter"] = "Role";
    objects["engineer"] = "Role";
    //Adding predicates to KB
    Predicates predicates;
    Args p1 = {std::make_pair("?r","Role"), std::make_pair("?l","Location")};
    Args p2 = {std::make_pair("?r","Role"), std::make_pair("?ps","Player_Status")};
    Args p3 = {std::make_pair("?v","Victim"), std::make_pair("?vt","Victim_Type")};
    Args p4 = {std::make_pair("?v","Victim"), std::make_pair("?vs","Victim_Status")};
    Args p5 = {std::make_pair("?r","Role"), std::make_pair("?v","Victim")};
    Args p6 = {std::make_pair("?r","Role")};
    Args p7 = {std::make_pair("?r","Role"), std::make_pair("?m","Marker_Type")};
    predicates.push_back(create_predicate("player_at", p1));
    predicates.push_back(create_predicate("player_status", p2));
    predicates.push_back(create_predicate("victim_type", p3));
    predicates.push_back(create_predicate("victim_status", p4));
    predicates.push_back(create_predicate("fov_victim", p5));
    predicates.push_back(create_predicate("fov_rubble", p6));
    predicates.push_back(create_predicate("fov_marker", p7));
    //Initialize KB
    this->kb = KnowledgeBase(predicates,objects,typetree); 
    //Can add facts now that KB is initialized.
    //Asked tell not to update the smt state string on its own to save time.
    this->kb.tell("(player_status medic safe)",false,false);
    this->kb.tell("(player_status transporter safe)",false,false);
    this->kb.tell("(player_status engineer safe)",false,false);
    for (int i = 1; i <= 35; i++) {
        this->kb.tell("(victim_status vic_" + to_string(i) + " unsaved)", false, false);
    }
    //Updates smt state string with all the new facts that were just added
    this->kb.update_state();
    this->medic_trapped_coord.push_back(0);
    this->medic_trapped_coord.push_back(0);
    this->transporter_trapped_coord.push_back(0);
    this->transporter_trapped_coord.push_back(0);
    this->engineer_trapped_coord.push_back(0);
    this->engineer_trapped_coord.push_back(0);
}
