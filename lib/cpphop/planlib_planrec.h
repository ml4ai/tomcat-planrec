#include <boost/json.hpp>
#include <limits>
#include <string>

namespace json = boost::json;


json::object seek_explanation(json::object planlib, std::vector<std::string> O) {
  double max_score = -std::numeric_limits<double>::infinity(); 
  json::object arg_max;
  for (auto& p : planlib["library"].as_array()) {
    if (O.size() <= p.as_object()["plan"].as_array().size()) {
      bool match = true;
      for (int i = 0; i < O.size(); i++) {
        std::string act = json::value_to<std::string>(p.as_object()["plan"].as_array()[i]);
        if (act.find(O[i]) == std::string::npos) {
          match = false;
          break;
        }
      }
      if (match) {
        if (p.as_object()["score"].as_double() > max_score) {
          arg_max = *p.if_object();
          max_score = json::value_to<double>(p.as_object()["score"]);
        }
      }
    }
  }
  return arg_max;
}
