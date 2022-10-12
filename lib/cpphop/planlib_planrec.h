#include <boost/json.hpp>
#include <limits>
#include <string>

namespace json = boost::json;


json::array seek_explanation(json::object planlib, std::vector<std::string> O) {
  double max_score = -std::numeric_limits<double>::infinity(); 
  json::array arg_maxes;
  for (auto& p : planlib["library"].as_array()) {
    if (O.size() <= p.as_object()["plan"].as_array().size()) {
      bool match = true;
      for (int i = 0; i < O.size(); i++) {
        if (p.as_object()["plan"].as_array()[i].as_string().find(O[i]) == json::string::npos) {
          match = false;
          break;
        }
      }
      if (match) {
        if (p.as_object()["score"].as_double() >= max_score) {
          if (p.as_object()["score"].as_double() > max_score) {
            arg_maxes.clear();
            arg_maxes.emplace_back(*p.if_object());
            max_score = json::value_to<double>(p.as_object()["score"]);
          }
          else {
            arg_maxes.emplace_back(*p.if_object());
          }
        }
      }
    }
  }
  return arg_maxes;
}
