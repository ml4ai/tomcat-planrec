#include "PercAgent.hpp"

#include "boost/json.hpp"
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

void PercAgent::process(mqtt::const_message_ptr msg) {
    json::object jv = json::parse(msg->to_string()).as_object();

    // Uncomment the line below to print the message
    try {
        if (jv.at("data").as_object().contains("locations")) {
            pretty_print(std::cout, jv.at("msg").at("sub_type"));
            pretty_print(std::cout, jv.at("data").at("callsign"));
            pretty_print(
                std::cout,
                jv.at("data")
                    .at("locations")
                    .at(jv.at("data").at("locations").as_array().size() - 1)
                    .at("id"));
        }
    }
    catch (exception& exc) {
        pretty_print(std::cout, jv);
    }
    //    cout << jv["data"].as_string() << endl;
}

PercAgent::PercAgent(string address) : Agent(address){};
