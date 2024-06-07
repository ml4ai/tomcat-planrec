#include <boost/program_options.hpp>
#include <iostream>
#include <sw/redis++/redis++.h>
#include "../../domains/pr_samples.h"

namespace po = boost::program_options;

using namespace sw::redis;

int main(int argc, char* argv[]) {
  std::string redis_address = "";
  std::string samples_key = "delivery_sample";
  std::string key = "actions";
  int samples = -1;

  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("redis_address,a",po::value<std::string>(),"redis address to redis database (string), default = none")
      ("samples_key,s", po::value<std::string>(), "map key for pr_samples.h (string), default = delivery_sample")
      ("key,k",po::value<std::string>(),"key to use for uploading actions to redis database (string), default = actions")
      ("samples,n", po::value<int>(),"number of sample actions to upload from pr_samples.h (int), default = -1 (all of them)")
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

    if (vm.count("samples_key")) {
      samples_key = vm["samples_key"].as<std::string>();
    }

    if (vm.count("key")) {
      key = vm["key"].as<std::string>();
    }

    if (vm.count("samples")) {
      samples = vm["samples"].as<int>();
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
    std::vector<std::pair<std::string,std::string>> obs = pr_samples[samples_key];
    std::vector<std::pair<std::string,std::string>> acts;
    if (samples > 0 && samples <= obs.size()) {
      acts = {obs.begin(),obs.begin() + samples};
    }
    else {
      acts = obs;
    }
    int i = 1;
    for (auto a : acts) {
      auto rank = std::to_string(i) + "-*";
      redis.xadd("actions",rank,{a});
      i++;
    }
  }
  catch (const Error &e) {
    std::cout << "Failed : " << e.what() << std::endl;
  }

  return EXIT_SUCCESS;
}
