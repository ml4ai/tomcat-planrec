#include "PercAgent.hpp"
#include "boost/json.hpp"
#include "file.hpp"
#include <iostream>

using namespace std;
namespace json = boost::json;

void pretty_print(std::ostream& os,
                  json::value const& jv,
                  std::string* indent = nullptr) {
    std::string indent_;
    if (!indent)
        indent = &indent_;
    switch (jv.kind()) {
    case json::kind::object: {
        os << "{\n";
        indent->append(4, ' ');
        auto const& obj = jv.get_object();
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
        auto const& arr = jv.get_array();
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

    vector<string> array;
    stringstream ss(str);
    std::string temp;
    while (ss >> temp)
        array.push_back(temp);
    return array;
}

void PercAgent::process(mqtt::const_message_ptr msg) {
    json::object jv = json::parse(msg->to_string()).as_object();
    std::string new_knowledge;
//    cout << msg->get_topic() << endl;
    if (msg->get_topic() == "observations/events/player/location") {
        try {
            if (jv.at("data").as_object().contains("locations")) {
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
                    jv.at("data").at("callsign"));
                if (role == "Red") {
                    new_knowledge += "medic ";
                }
                else if (role == "Green") {
                    new_knowledge += "transporter ";
                }
                else {
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
        catch (exception& exc) {
            cout << exc.what() << endl;
//            pretty_print(std::cout, jv);
        }
    }
    else if (msg->get_topic() == "observations/events/player/rubble_collapse") {
        try {
            pretty_print(std::cout, jv.at("msg").at("sub_type"));
            pretty_print(std::cout, jv.at("data").at("playername"));
            pretty_print(std::cout, jv.at("data").at("fromBlock_x"));
            pretty_print(std::cout, jv.at("data").at("fromBlock_z"));
            auto player_color =
                split_player_name(
                    jv.at("data").at("playername").as_string().c_str())
                    .at(0);
            if (player_color == "RED") {
                this->medic_trapped_coord.at(0) =
                    (int)jv.at("data").at("fromBlock_x").as_int64();
                this->medic_trapped_coord.at(1) =
                    (int)jv.at("data").at("fromBlock_z").as_int64();
            }
            else if (player_color == "GREEN") {
                this->transporter_trapped_coord.at(0) =
                    (int)jv.at("data").at("fromBlock_x").as_int64();
                this->transporter_trapped_coord.at(1) =
                    (int)jv.at("data").at("fromBlock_z").as_int64();
            }
            else {
                this->engineer_trapped_coord.at(0) =
                    (int)jv.at("data").at("fromBlock_x").as_int64();
                this->engineer_trapped_coord.at(1) =
                    (int)jv.at("data").at("fromBlock_z").as_int64();
            }
            new_knowledge = "(player_status ";
            if (player_color == "RED") {
                new_knowledge += "medic trapped)";
            }
            else if (player_color == "GREEN") {
                new_knowledge += "transporter trapped)";
            }
            else {
                new_knowledge += "engineer trapped)";
            }
            tell(this->kb, new_knowledge);
        }

        catch (exception& exc) {
            cout << exc.what() << endl;
            pretty_print(std::cout, jv);
            cout << endl;
        }
    }
    else if (msg->get_topic() ==
             "observations/events/player/rubble_destroyed") {
        try {
            pretty_print(std::cout, jv.at("msg").at("sub_type"));
            pretty_print(std::cout, jv.at("data").at("rubble_x"));
            pretty_print(std::cout, jv.at("data").at("rubble_z"));

            auto rubble_x = (int)jv.at("data").at("rubble_x").as_int64();
            auto rubble_z = (int)jv.at("data").at("rubble_z").as_int64();
            new_knowledge = "(player_status";
            if (rubble_x == this->medic_trapped_coord.at(0) and
                rubble_z == this->medic_trapped_coord.at(1)) {
                new_knowledge += " medic safe)";
                this->medic_trapped_coord.at(0) = 0;
                this->medic_trapped_coord.at(1) = 0;
                tell(this->kb, new_knowledge);
            }
            else if (rubble_x == this->transporter_trapped_coord.at(0) and
                     rubble_z == this->transporter_trapped_coord.at(1)) {
                new_knowledge += " transporter safe)";
                this->transporter_trapped_coord.at(0) = 0;
                this->transporter_trapped_coord.at(1) = 0;
                tell(this->kb, new_knowledge);
            }
            else if (rubble_x == this->engineer_trapped_coord.at(0) and
                     rubble_z == this->engineer_trapped_coord.at(1)) {
                new_knowledge += " engineer safe)";
                this->engineer_trapped_coord.at(0) = 0;
                this->engineer_trapped_coord.at(1) = 0;
                tell(this->kb, new_knowledge);
            }
        }
        catch (exception& exc) {
            cout << exc.what() << endl;
            pretty_print(std::cout, jv);
        }
    }
}

PercAgent::PercAgent(string address) : Agent(address) {
    // initialize kb
    auto const s = read_file("../../../metadata/Saturn_2.6_3D_sm_v1.0.json");
    json::object jv = json::parse(s).as_object();
    vector<string> location_ids;
    for (const auto& loc : jv.at("locations").as_array()) {
        location_ids.emplace_back(loc.at("id").as_string().c_str());
    }
    location_ids.emplace_back("UNKNOWN");
    initialize_data_type(this->kb, "Location", location_ids);
    initialize_data_type(this->kb, "Player_Status", {"safe", "trapped"});
    initialize_data_type(
        this->kb, "Role", {"medic", "transporter", "engineer"});
    initialize_predicate(this->kb, "player_at", {"Role", "Location"});
    initialize_predicate(this->kb, "player_status", {"Role", "Player_Status"});
    tell(this->kb, "(player_status medic safe)");
    tell(this->kb, "(player_status transporter safe)");
    tell(this->kb, "(player_status engineer safe)");
    this->medic_trapped_coord.push_back(0);
    this->medic_trapped_coord.push_back(0);
    this->transporter_trapped_coord.push_back(0);
    this->transporter_trapped_coord.push_back(0);
    this->engineer_trapped_coord.push_back(0);
    this->engineer_trapped_coord.push_back(0);
}
