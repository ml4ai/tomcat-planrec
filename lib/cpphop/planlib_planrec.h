#include <boost/json.hpp>
#include <limits>
#include <string>

namespace json = boost::json;


json::object seek_explanation(json::object planlib, std::vector<std::string> O) {
  double max_score = -std::numeric_limits<double>::infinity(); 
  json::object arg_max;
  for (auto const& p : planlib["library"].as_array()) {
    if (O.size() <= p["plan"].as_array().size()) {
      bool match = true;
      for (int i = 0; i < O.size(); i++) {
        std::string act = json::value_to<std::string>(p["plan"].as_array()[i]);
        if (act.find(O[i]) == std::string::npos) {
          match = false;
          break;
        }
      }
      if (match) {
        if (p["score"].as_double() > max_score) {
          arg_max = p;
          max_score = p["score"].as_double();
        }
      }
    }
  }
  return arg_max;
}
