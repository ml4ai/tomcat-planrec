#include "PercAgent.hpp"
#include "boost/json.hpp"
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

void process_fov(KnowledgeBase &kb, const std::string &role, std::queue<int> que) {
    std::queue<int> tmp_queue;
    std::set<int> tmp_set;
    tmp_queue = que;
    std::string new_knowledge;

    while (!tmp_queue.empty()) {
        new_knowledge = "(fov_victim " + role;
        if (tmp_queue.front() == -1 or (tmp_set.find(tmp_queue.front()) != tmp_set.end())) {
            tmp_queue.pop();
        } else {
            new_knowledge += " vic_" + to_string(tmp_queue.front());
            tmp_queue.pop();
        }
        tell(kb, new_knowledge, -1, false);
    }
}

void PercAgent::process(mqtt::const_message_ptr msg) {
    json::value jv = json::parse(msg->to_string()).as_object();
    std::string new_knowledge;
//    cout << msg->get_topic() << endl;
    if (msg->get_topic() == "ground_truth/mission/victims_list") {
        std::vector<std::string> vic_types;
        for (const auto &v: jv.at_pointer("/data/mission_victim_list").as_array()) {
            if (v.at("block_type").as_string() == "block_victim_proximity") {
                vic_types.emplace_back("c");
            } else if (v.at("block_type").as_string() == "block_victim_1") {
                vic_types.emplace_back("a");
            } else {
                vic_types.emplace_back("b");
            }
        }
        initialize_data_type(this->kb, "Victim_Type", {"a", "b", "c"});
        std::string knowledge;
        for (int i = 0; i < vic_types.size(); i++) {
            knowledge = "(victim_type vic_" + to_string(i + 1) + " " + vic_types[i] + ")";
            tell(this->kb, knowledge);
        }
    } else if (msg->get_topic() == "observations/events/player/location") {
        try {
            if (jv.at_pointer("/data").as_object().contains("locations")) {
//                pretty_print(std::cout, jv.at("msg").at("sub_type"));
//                pretty_print(std::cout, jv.at("data").at("callsign"));
//                pretty_print(
//                    std::cout,
//                    jv.at("data")
//                        .at("locations")
//                        .at(jv.at("data").at("locations").as_array().size() - 1)
//                        .at("id"));
                new_knowledge = "(player_at ";
                auto role = boost::json::value_to<std::string>(
                        jv.at_pointer("/data/callsign"));
                if (role == "Red") {
                    new_knowledge += "medic ";
                } else if (role == "Green") {
                    new_knowledge += "transporter ";
                } else {
                    new_knowledge += "engineer ";
                }
                new_knowledge += boost::json::value_to<std::string>(
                        jv.at("data")
                                .at("locations")
                                .at(jv.at("data").at("locations").as_array().size() - 1)
                                .at("id"));
                new_knowledge += ")";
                tell(this->kb, new_knowledge);
            }
        }
        catch (exception &exc) {
            cout << exc.what() << endl;
//            pretty_print(std::cout, jv);
        }
    } else if (msg->get_topic() == "observations/events/player/rubble_collapse") {
        try {
            pretty_print(std::cout, jv.at_pointer("/msg/sub_type"));
            pretty_print(std::cout, jv.at_pointer("/data/playername"));
            pretty_print(std::cout, jv.at_pointer("/data/fromBlock_x"));
            pretty_print(std::cout, jv.at_pointer("/data/fromBlock_z"));
            auto player_color =
                    split_player_name(
                            jv.at_pointer("/data/playername").as_string().c_str())
                            .at(0);
            if (player_color == "RED") {
                this->medic_trapped_coord.at(0) =
                        (int) jv.at_pointer("/data/fromBlock_x").as_int64();
                this->medic_trapped_coord.at(1) =
                        (int) jv.at_pointer("/data/fromBlock_z").as_int64();
            } else if (player_color == "GREEN") {
                this->transporter_trapped_coord.at(0) =
                        (int) jv.at_pointer("/data/fromBlock_x").as_int64();
                this->transporter_trapped_coord.at(1) =
                        (int) jv.at_pointer("/data/fromBlock_z").as_int64();
            } else {
                this->engineer_trapped_coord.at(0) =
                        (int) jv.at_pointer("/data/fromBlock_x").as_int64();
                this->engineer_trapped_coord.at(1) =
                        (int) jv.at_pointer("/data/fromBlock_z").as_int64();
            }
            new_knowledge = "(player_status ";
            if (player_color == "RED") {
                new_knowledge += "medic trapped)";
            } else if (player_color == "GREEN") {
                new_knowledge += "transporter trapped)";
            } else {
                new_knowledge += "engineer trapped)";
            }
            tell(this->kb, new_knowledge);
        }

        catch (exception &exc) {
            cout << exc.what() << endl;
            pretty_print(std::cout, jv);
            cout << endl;
        }
    } else if (msg->get_topic() ==
               "observations/events/player/rubble_destroyed") {
        try {
            pretty_print(std::cout, jv.at_pointer("/msg/sub_type"));
            pretty_print(std::cout, jv.at_pointer("/data/rubble_x"));
            pretty_print(std::cout, jv.at_pointer("/data/rubble_z"));

            auto rubble_x = (int) jv.at_pointer("/data/rubble_x").as_int64();
            auto rubble_z = (int) jv.at_pointer("/data/rubble_z").as_int64();
            new_knowledge = "(player_status";
            if (rubble_x == this->medic_trapped_coord.at(0) and
                rubble_z == this->medic_trapped_coord.at(1)) {
                new_knowledge += " medic safe)";
                this->medic_trapped_coord.at(0) = 0;
                this->medic_trapped_coord.at(1) = 0;
                tell(this->kb, new_knowledge);
            } else if (rubble_x == this->transporter_trapped_coord.at(0) and
                       rubble_z == this->transporter_trapped_coord.at(1)) {
                new_knowledge += " transporter safe)";
                this->transporter_trapped_coord.at(0) = 0;
                this->transporter_trapped_coord.at(1) = 0;
                tell(this->kb, new_knowledge);
            } else if (rubble_x == this->engineer_trapped_coord.at(0) and
                       rubble_z == this->engineer_trapped_coord.at(1)) {
                new_knowledge += " engineer safe)";
                this->engineer_trapped_coord.at(0) = 0;
                this->engineer_trapped_coord.at(1) = 0;
                tell(this->kb, new_knowledge);
            }
        }
        catch (exception &exc) {
            cout << exc.what() << endl;
            pretty_print(std::cout, jv);
        }
    } else if (msg->get_topic() ==
               "agent/pygl_fov/player/3d/summary") {
        try {
            for (auto v: jv.at_pointer("/data/blocks").as_array()) {
                if (this->fov_medic.size() == FOV_STACK_SIZE) {
                    clear_fov_facts(this->kb, "fov_victim", "medic");
                    clear_fov_facts(this->kb, "fov_rubble", "medic");
                    clear_fov_facts(this->kb, "fov_marker", "medic");
                    set<int> int_set(this->fov_medic.begin(), this->fov_medic.end());
//                    this->fov_medic.assign(int_set.begin(), int_set.end());
                    for (auto obj: int_set) {
                        if (obj >= 0) {
                            new_knowledge = "(fov_victim medic vic_" + to_string(obj) + ")";
                            tell(this->kb, new_knowledge, -1, false);
                        } else if (obj == -10) {
                            new_knowledge = "(fov_rubble medic)";
                            tell(this->kb, new_knowledge, -1, false);
                        } else if (obj <= -100) {
                            // {"novictim": -101, "regularvictim": -102, "criticalvictim": -103, "threat": -104, "bonedamage": -105}
                            if (obj == -101) {
                                new_knowledge = "(fov_marker medic novictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -102) {
                                new_knowledge = "(fov_marker medic regularvictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -103) {
                                new_knowledge = "(fov_marker medic criticalvictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -104) {
                                new_knowledge = "(fov_marker medic threat)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -105) {
                                new_knowledge = "(fov_marker medic bonedamage)";
                                tell(this->kb, new_knowledge, -1, false);
                            }
                        }

                    }
                    this->fov_medic = {};
                } else if (this->fov_engineer.size() == FOV_STACK_SIZE) {
                    clear_fov_facts(this->kb, "fov_victim", "engineer");
                    clear_fov_facts(this->kb, "fov_rubble", "engineer");
                    clear_fov_facts(this->kb, "fov_marker", "engineer");
                    set<int> int_set(this->fov_engineer.begin(), this->fov_engineer.end());
//                    this->fov_medic.assign(int_set.begin(), int_set.end());
                    for (auto obj: int_set) {
                        new_knowledge = "(fov_victim engineer vic_";
                        if (obj >= 0) {
                            new_knowledge += to_string(obj) + ")";
                            tell(this->kb, new_knowledge, -1, false);
                        } else if (obj == -10) {
                            new_knowledge = "(fov_rubble engineer)";
                            tell(this->kb, new_knowledge, -1, false);
                        } else if (obj <= -100) {
                            // {"novictim": -101, "regularvictim": -102, "criticalvictim": -103, "threat": -104, "bonedamage": -105}
                            if (obj == -101) {
                                new_knowledge = "(fov_marker engineer novictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -102) {
                                new_knowledge = "(fov_marker engineer regularvictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -103) {
                                new_knowledge = "(fov_marker engineer criticalvictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -104) {
                                new_knowledge = "(fov_marker engineer threat)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -105) {
                                new_knowledge = "(fov_marker engineer bonedamage)";
                                tell(this->kb, new_knowledge, -1, false);
                            }
                        }
                    }
                    this->fov_engineer = {};
                } else if (this->fov_transporter.size() == FOV_STACK_SIZE) {
                    clear_fov_facts(this->kb, "fov_victim", "transporter");
                    clear_fov_facts(this->kb, "fov_rubble", "transporter");
                    clear_fov_facts(this->kb, "fov_marker", "transporter");
                    set<int> int_set(this->fov_transporter.begin(), this->fov_transporter.end());
//                    this->fov_medic.assign(int_set.begin(), int_set.end());
                    for (auto obj: int_set) {
                        new_knowledge = "(fov_victim transporter vic_";
                        if (obj >= 0) {
                            new_knowledge += to_string(obj) + ")";
                            tell(this->kb, new_knowledge, -1, false);
                        } else if (obj == -10) {
                            new_knowledge = "(fov_rubble transporter)";
                            tell(this->kb, new_knowledge, -1, false);
                        } else if (obj <= -100) {
                            // {"novictim": -101, "regularvictim": -102, "criticalvictim": -103, "threat": -104, "bonedamage": -105}
                            if (obj == -101) {
                                new_knowledge = "(fov_marker transporter novictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -102) {
                                new_knowledge = "(fov_marker transporter regularvictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -103) {
                                new_knowledge = "(fov_marker transporter criticalvictim)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -104) {
                                new_knowledge = "(fov_marker transporter threat)";
                                tell(this->kb, new_knowledge, -1, false);
                            } else if (obj == -105) {
                                new_knowledge = "(fov_marker transporter bonedamage)";
                                tell(this->kb, new_knowledge, -1, false);
                            }
                        }
                    }
                    this->fov_transporter = {};
                }

                auto player_color =
                        split_player_name(
                                jv.at_pointer("/data/playername").as_string().c_str())
                                .at(0);
                if (v.at_pointer("/type").as_string().find("victim") != std::string::npos) {
//                    pretty_print(std::cout, jv.at_pointer("/data/playername"));
//                    pretty_print(std::cout, v.at_pointer("/id"));
                    if (player_color == "RED") {
                        this->fov_medic.push_back(int(v.at_pointer("/id").as_int64()));
                    } else if (player_color == "BLUE") {
                        this->fov_engineer.push_back(int(v.at_pointer("/id").as_int64()));
                    } else {
                        this->fov_transporter.push_back(int(v.at_pointer("/id").as_int64()));
                    }
                } else if (v.at_pointer("/type").as_string().find("gravel") != std::string::npos) {
                    // encode rubble as -10
                    if (player_color == "RED") {
                        this->fov_medic.push_back(-10);
                    } else if (player_color == "BLUE") {
                        this->fov_engineer.push_back(-10);
                    } else {
                        this->fov_transporter.push_back(-10);
                    }
                } else if (v.at_pointer("/type").as_string().find("marker_block") != std::string::npos) {
//                    pretty_print(std::cout, v.at_pointer("/marker_type"));
                    // {"novictim": -101, "regularvictim": -102, "criticalvictim": -103, "threat": -104, "bonedamage": -105}
                    if (player_color == "RED") {
                        if (v.at_pointer("/marker_type").as_string().find("novictim") != std::string::npos) {
                            this->fov_medic.push_back(-101);
                        } else if (v.at_pointer("/marker_type").as_string().find("regularvictim") !=
                                   std::string::npos) {
                            this->fov_medic.push_back(-102);
                        } else if (v.at_pointer("/marker_type").as_string().find("criticalvictim") !=
                                   std::string::npos) {
                            this->fov_medic.push_back(-103);
                        } else if (v.at_pointer("/marker_type").as_string().find("threat") != std::string::npos) {
                            this->fov_medic.push_back(-104);
                        } else if (v.at_pointer("/marker_type").as_string().find("bonedamage") != std::string::npos) {
                            this->fov_medic.push_back(-105);
                        }
                    } else if (player_color == "BLUE") {
                        if (v.at_pointer("/marker_type").as_string().find("novictim") != std::string::npos) {
                            this->fov_engineer.push_back(-101);
                        } else if (v.at_pointer("/marker_type").as_string().find("regularvictim") !=
                                   std::string::npos) {
                            this->fov_engineer.push_back(-102);
                        } else if (v.at_pointer("/marker_type").as_string().find("criticalvictim") !=
                                   std::string::npos) {
                            this->fov_engineer.push_back(-103);
                        } else if (v.at_pointer("/marker_type").as_string().find("threat") != std::string::npos) {
                            this->fov_engineer.push_back(-104);
                        } else if (v.at_pointer("/marker_type").as_string().find("bonedamage") != std::string::npos) {
                            this->fov_engineer.push_back(-105);
                        }
                    } else {
                        if (v.at_pointer("/marker_type").as_string().find("novictim") != std::string::npos) {
                            this->fov_transporter.push_back(-101);
                        } else if (v.at_pointer("/marker_type").as_string().find("regularvictim") !=
                                   std::string::npos) {
                            this->fov_transporter.push_back(-102);
                        } else if (v.at_pointer("/marker_type").as_string().find("criticalvictim") !=
                                   std::string::npos) {
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
                // tell(this->kb, "(player_status medic safe)");
//                clear_facts(this->kb, "fov_victim");
//                cout << this->fov_medic.size() << endl;
//                cout << this->fov_engineer.size() << endl;
//                cout << this->fov_transporter.size() << endl;
//                cout << std::all_of(this->fov_medic.begin(), this->fov_medic.end(), [](int i) { return i == -1; })
//                     << endl;
            }
        }
        catch (exception &exc) {
            cout << exc.what() << endl;
        }


    } else if (msg->get_topic() ==
               "observations/events/player/triage") {
        try {
            if (jv.at_pointer("/data/triage_state") == "SUCCESSFUL") {
                tell(this->kb,
                     "(victim_status vic_" + to_string(jv.at_pointer("/data/victim_id").as_int64()) +
                     " saved)");
            }
        }
        catch (exception &exc) {
            cout << exc.what() << endl;
        }
    }

}

PercAgent::PercAgent(string
                     address) : Agent(address) {
    // initialize kb
    auto const s = read_file("../../../metadata/Saturn_2.6_3D_sm_v1.0.json");
    json::object jv = json::parse(s).as_object();
    vector<string> location_ids;
    for (const auto &loc: jv.at("locations").as_array()) {
        location_ids.emplace_back(loc.at("id").as_string().c_str());
    }
    location_ids.emplace_back("UNKNOWN");

    initialize_data_type(this->kb, "Location", location_ids);
    initialize_data_type(this->kb, "Player_Status", {"safe", "trapped"});
    std::vector<std::string> vic_ids;
    for (int i = 1; i <= 35; i++) {
        vic_ids.push_back("vic_" + to_string(i));
    }
    initialize_data_type(this->kb, "Victim", vic_ids);
    initialize_data_type(this->kb, "Victim_Type", {"a", "b", "c"});
    initialize_data_type(this->kb, "Victim_Status", {"unsaved", "saved"});
    initialize_data_type(this->kb, "Marker_Type",
                         {"novictim", "regularvictim", "criticalvictim", "threat", "bonedamage"});
    initialize_data_type(
            this->kb, "Role", {"medic", "transporter", "engineer"});
    initialize_predicate(this->kb, "player_at", {"Role", "Location"});
    initialize_predicate(this->kb, "player_status", {"Role", "Player_Status"});
    initialize_predicate(this->kb, "victim_type", {"Victim", "Victim_Type"});
    initialize_predicate(this->kb, "victim_status", {"Victim", "Victim_Status"});
    initialize_predicate(this->kb, "fov_victim", {"Role", "Victim"});
    initialize_predicate(this->kb, "fov_rubble", {"Role"});
    initialize_predicate(this->kb, "fov_marker", {"Role", "Marker_Type"});

    tell(this->kb, "(player_status medic safe)");
    tell(this->kb, "(player_status transporter safe)");
    tell(this->kb, "(player_status engineer safe)");

    for (int i = 1; i <= 35; i++) {
        tell(this->kb, "(victim_status vic_" + to_string(i) + " unsaved)");
    }

    this->medic_trapped_coord.push_back(0);
    this->medic_trapped_coord.push_back(0);
    this->transporter_trapped_coord.push_back(0);
    this->transporter_trapped_coord.push_back(0);
    this->engineer_trapped_coord.push_back(0);
    this->engineer_trapped_coord.push_back(0);
}
