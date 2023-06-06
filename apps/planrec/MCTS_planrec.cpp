#include "../../domains/score_functions.h"
#include "../../domains/r_maps.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include <boost/program_options.hpp>
#include "cpphop/loader.h"
#include "cpphop/cppMCTSplanrec.h"
#include "util.h"
#include <chrono>
namespace po = boost::program_options;

using namespace std;

int main(int argc, char* argv[]) {
  int time_limit = 1000;
  int r = 5;
  double c = sqrt(2.0);
  int seed = 2022;
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string score_fun = "delivery_one";
  std::string r_map = "transport_reach_map";
  std::string redis_address = "";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("time_limit,T", po::value<int>(), "Time limit (in milliseconds) allowed for plan recognition (int), default = 1000")
      ("simulations,r", po::value<int>(), "Number of simulations per resource cycle (int), default = 5")
      ("exp_param,c",po::value<double>(),"The exploration parameter for the planner (double), default = sqrt(2)")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("score_fun,F",po::value<std::string>(),"name of score function for (string), default = delivery_one")
      ("reach_map,m",po::value<std::string>(),"name of reachability map (string), default = transport_reach_map")
      ("seed,s", po::value<int>(),"Random Seed (int)")
      ("redis_address,a",po::value<std::string>(), "Address to redis server, default = (none, no connection)")
    ;

    po::variables_map vm;        
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("time_limit")) {
      time_limit = vm["time_limit"].as<int>();
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

    if (vm.count("reach_map")) {
      r_map = vm["reach_map"].as<std::string>();
    }

    if (vm.count("seed")) {
      seed = vm["seed"].as<int>();
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
  std::vector<std::pair<int, std::string>> actions;
  update_actions(redis_address,actions);
  auto res = cppMCTSplanrec(domain,problem,reach_maps[r_map],scorers[score_fun],actions,time_limit,r,c,seed,redis_address); 
  std::vector<std::string> acts;
  for (auto [a,_] : domain.actions) {
    acts.push_back(a);
  }
  upload_plan_explanation(redis_address,res.tasktree,res.t[res.end].plan,acts,res.t[res.end].tasks,res.t[res.end].state.get_facts());
  return EXIT_SUCCESS;
}
