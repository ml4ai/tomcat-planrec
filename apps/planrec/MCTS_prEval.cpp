#include "../../domains/score_functions.h"
#include "../../domains/pr_samples.h"
 #include "../../domains/r_maps.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include <boost/program_options.hpp>
#include "cpphop/loader.h"
#include "cpphop/cppMCTSplanrec.h"
#include "cpphop/grapher.h"
#include <chrono>
namespace po = boost::program_options;

using namespace std;

int main(int argc, char* argv[]) {
  int R = 30;
  double c = sqrt(2.0);
  int seed = 2022;
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string score_fun = "delivery_one";
  std::string r_map = "transport_reach_map";
  std::string sample = "delivery_sample";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int), default = 30")
      ("exp_param,c",po::value<double>(),"The exploration parameter for the planner (double), default = sqrt(2)")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("score_fun,F",po::value<std::string>(),"name of score function (string), default = delivery_one")
      ("reach_map,m",po::value<std::string>(),"name of reachability map (string), default = transport_reach_map")
      ("sample,S",po::value<std::string>(),"Plan Rec sample (string), default = delivery_sample")
      ("seed,s", po::value<int>(),"Random Seed (int)")
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

    if (vm.count("sample")) {
      sample = vm["sample"].as<std::string>();
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
  auto first = pr_samples[sample].begin();
  double count = 0;
  double trials = 0;
  for (int i = 1; i < pr_samples[sample].size(); i++) {
    trials++;
    auto last = pr_samples[sample].begin() + i;
    std::vector<std::string> given_plan(first,last);
    std::string ground_truth = pr_samples[sample][i];
    auto results = cppMCTSplanrec(domain,problem,given_plan,reach_maps[r_map],scorers[score_fun],R,c,seed,1); 
    std::string pred = results.t[results.end].plan.back();
    cout << "Observations: " << given_plan.size() << ", ";
    if (pred.find(ground_truth) != std::string::npos) {
      cout << "correct ";
      count++; 
    }
    else {
      cout << "incorrect ";
    }
    cout << "action prediction!" << endl;
  }
  cout << endl;
  
  cout << "Average Accuracy: " << count/trials << endl;
  return EXIT_SUCCESS;
}
