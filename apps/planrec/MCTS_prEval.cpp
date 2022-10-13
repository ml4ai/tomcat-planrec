#include "../../domains/score_functions.h"
#include "../../domains/pr_samples.h"
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
  double eps = 0.4;
  int successes = 19;
  double prob = 0.75;
  int seed = 2022;
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string score_fun = "delivery_one";
  std::string sample = "delivery_sample";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int), default = 30")
      ("exp_param,e",po::value<double>(),"The exploration parameter for the planner (double), default = 0.4")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("score_fun,F",po::value<std::string>(),"name of score function (string), default = delivery_one")
      ("sample,S",po::value<std::string>(),"Plan Rec sample (string), default = delivery_sample")
      ("horizon_s,hs",po::value<int>(),"Average depth number for horizon sampler (int), default = 19")
      ("horizon_prob,hp",po::value<double>(),"Failure probability for horizon sampler (double), default = 0.75")
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
      eps = vm["exp_param"].as<double>();
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

    if (vm.count("horizon_s")) {
      successes = vm["horizon_s"].as<int>();
    }

    if (vm.count("horizon_prob")) {
      prob = vm["horizon_prob"].as<double>();
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
    auto results = cppMCTSplanrec(domain,problem,given_plan,scorers[score_fun],R,eps,successes,prob,seed,1); 
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
