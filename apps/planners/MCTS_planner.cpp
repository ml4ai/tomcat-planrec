#include "domains/score_functions.h"
#include <math.h>
#include <stdlib.h>
//#include "plan_trace.h"
//#include "plangrapher.h"
#include <istream>
#include <nlohmann/json.hpp>
#include <boost/program_options.hpp>
#include "cpphop/loader.h"
#include "cpphop/cppMCTShop.h"
namespace po = boost::program_options;

using json = nlohmann::json;

using namespace std;

int main(int argc, char* argv[]) {
  int plan_size = -1;
  int R = 30;
  double eps = 0.4;
  int seed = 2022;
  std::string dom_file = "../apps/planners/domains/storage_domain.hddl";
  std::string prob_file = "../apps/planners/domains/storage_problem.hddl";
  std::string score_fun = "delivery_one";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int)")
      ("plan_size,ps",po::value<int>(),"Number of actions to return (int), default value of -1 returns full plan")
      ("exp_param,e",po::value<double>(),"The exploration parameter for the planner (double)")
      ("dom_file,D", po::value<std::string>(),"domain file (string)")
      ("prob_file,P",po::value<std::string>(),"problem file (string)")
      ("score_fun,F",po::value<std::string>(),"name of score function (string)")
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

    if (vm.count("plan_size")) {
      plan_size = vm["plan_size"].as<int>();
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
    if (vm.count("seed")) {
      seed = vm["seed"].as<int>();
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
  cppMCTShop(domain,problem,scorers[score_fun],R,plan_size,eps,seed); 
  return EXIT_SUCCESS;
}
