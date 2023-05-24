#include "../../domains/score_functions.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include <boost/program_options.hpp>
#include "cpphop/loader.h"
#include "cpphop/cppMCTSeval.h"
#include <chrono>
namespace po = boost::program_options;

using namespace std;

int main(int argc, char* argv[]) {
  int R = 30;
  int r = 5;
  double c = sqrt(2.0);
  int seed = 2022;
  int trials = 10;
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string score_fun = "delivery_one";
  std::string redis_address = "";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int), default = 30")
      ("simulations,r", po::value<int>(), "Number of simulations per resource cycle (int), default = 5")
      ("exp_param,c",po::value<double>(),"The exploration parameter for the planner (double), default = sqrt(2)")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("score_fun,F",po::value<std::string>(),"name of score function (string), default = delivery_one")
      ("seed,s", po::value<int>(),"Random Seed (int)")
      ("trials,t",po::value<int>(),"Number of trials (with different seeds) per eval cycle (int), default = 10")
      ("redis_address,a",po::value<std::string>(), "Address to redis server, default = (none, no connection)")
    ;

    po::variables_map vm;        
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("resource_cycles")) {
      R = vm["resource_cycles"].as<int>();
    }

    if (vm.count("simulations")) {
      r = vm["simulations"].as<int>();
    }

    if (vm.count("exp_param")) {
      c = vm["exp_param"].as<double>();
    }

    if (vm.count("dom_file")) {
      dom_file = vm["dom_file"].as<std::string>();
    }

    if (vm.count("prob_file")) {
      prob_file = vm["prob_file"].as<std::string>();
    }

    if (vm.count("score_fun")) {
      score_fun = vm["score_fun"].as<std::string>();
    }

    if (vm.count("seed")) {
      seed = vm["seed"].as<int>();
    }

    if (vm.count("trials")) {
      trials = vm["trials"].as<int>();
    }

    if (vm.count("redis_address")) {
      redis_address = vm["redis_address"].as<std::string>();
    }
  }
  catch(std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  catch(...) {
    std::cerr << "Exception of unknown type!\n";
  }
  auto [domain,problem] = load(dom_file,prob_file);
  if (redis_address != "") {
    Redis_Connect* rc = Redis_Connect::getInstance(redis_address);
    std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> act_results;
    std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> exp_results;
    rc->redis.xrange("actions","-","+",std::back_inserter(act_results));
    rc->redis.xrange("explanations","-","+",std::back_inserter(exp_results));
    int i = 0;
    for (auto ex : exp_results) {
      for (auto ey : ex.second) {
        json::value j = json::parse(ey.second);
        TaskGraph taskgraph = json::value_to<TaskGraph>(j.as_object()["taskgraph"]);
        std::unordered_map<std::string, std::vector<std::string>> 
          facts = json::value_to<std::unordered_map<std::string, std::vector<std::string>>>(j.as_object()["state"]);
        std::vector<int> times;
        std::vector<std::string> actions;
        for (int j = i + 1; j < act_results.size(); j++) {
          times.push_back(std::stoi(act_results[j].first)); 
          for (auto a : act_results[j].second) {
            actions.push_back(a.second);
          }
          double acc = 0.0;
          for (int k = 0; k < trials; k++) {
            auto pred = cppMCTSeval(domain,
                                    problem,
                                    scorers[score_fun],
                                    taskgraph,
                                    facts,
                                    times,
                                    R,
                                    r,
                                    c,
                                    seed,
                                    redis_address);
            bool match = true;
            for (int l = 0; l < pred.size(); l++) {
              if (pred[l].find(actions[l]) == std::string::npos) {
                match = false;
                break;
              }
            }

            if (match) {
              acc += 1.0;
            }
            seed += 100;
          }
          acc /= trials; 
          std::cout << "observations: " << i + 1 << ", prediction horizon: ";
          std::cout << j << ", average accuracy over " << trials << " trials: ";
          std::cout << acc << std::endl;
        }
        std::cout << std::endl;
        i++;
      }
    }
  }
  else {
    std::cout << "No redis server address given, shutting down!" << std::endl; 
  }
  return EXIT_SUCCESS;
}
