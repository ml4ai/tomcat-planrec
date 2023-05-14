#include <boost/program_options.hpp>
#include <boost/json.hpp>
#include <iostream>
#include <fstream>
#include <sw/redis++/redis++.h>

namespace json = boost::json;
namespace po = boost::program_options;

using namespace sw::redis;

int main(int argc, char* argv[]) {
  std::string redis_address = "";
  std::string save_path = "../data";
  std::string key = "explanations";
  std::string lower = "-";
  std::string upper = "+";

  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("redis_address,a",po::value<std::string>(),"redis address to redis database (string), default = none")
      ("save_path,s", po::value<std::string>(), "path to where outputted files are saved (string), default = ../data")
      ("key,k",po::value<std::string>(),"database key, also used to name json files (string), default = explanations")
      ("lower_bound,l", po::value<std::string>(),"lower bound for redis retrieval (string), default = -")
      ("upper_bound,u", po::value<std::string>(),"upper bound for redis retrieval (string), default = +")
    ;

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("redis_address")) {
      redis_address = vm["redis_address"].as<std::string>();
    }

    if (vm.count("save_path")) {
      save_path = vm["save_path"].as<std::string>();
    }

    if (vm.count("key")) {
      key = vm["key"].as<std::string>();
    }

    if (vm.count("lower_bound")) {
      lower = vm["lower_bound"].as<std::string>();
    }

    if (vm.count("upper_bound")) {
      upper = vm["upper_bound"].as<std::string>();
    }

  }
  catch(std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  catch(...) {
    std::cerr << "Exception of unknown type!\n";
  }
  
  try {
    auto redis = Redis(redis_address);
    std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> xresults;
    redis.xrange(key,lower,upper,std::back_inserter(xresults));
    int i = 0;
    for (auto x : xresults) {
      for (auto y : x.second) {
        std::string f = save_path + "/" + key + "_" + std::to_string(i) + ".json";
        std::ofstream o(f); 
        i++;
        json::value g = json::parse(y.second);
        o << std::setw(4) << g << std::endl; 
      }
    }
  }
  catch (const Error &e) {
    std::cout << "Failed : " << e.what() << std::endl;
  }

  return EXIT_SUCCESS;
}
