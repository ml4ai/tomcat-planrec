#include "../../domains/score_functions.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include <boost/program_options.hpp>
#include "cpphop/loader.h"
#include "cpphop/cppMCTShop.h"
#include "cpphop/grapher.h"
#include <chrono>
namespace po = boost::program_options;

using namespace std;

int main(int argc, char* argv[]) {
  int plan_size = -1;
  int R = 30;
  double c = sqrt(2.0);
  int seed = 2022;
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string score_fun = "delivery_one";
  bool graph = false;
  std::string graph_file = "";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("resource_cycles,R", po::value<int>(), "Number of resource cycles allowed for each search action (int), default = 30")
      ("plan_size,ps",po::value<int>(),"Number of actions to return (int), default value of -1 returns full plan")
      ("exp_param,c",po::value<double>(),"The exploration parameter for the planner (double), default = sqrt(2)")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("score_fun,F",po::value<std::string>(),"name of score function (string), default = delivery_one")
      ("seed,s", po::value<int>(),"Random Seed (int)")
      ("graph,g",po::bool_switch()->default_value(false),"Creates a task tree graph of the returned plan and saves it as a png, default = false")
      ("graph_file,gf",po::value<std::string>(), "File name for created graph (string), default = name of problem definition")
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

    if (vm.count("graph")) {
      graph = vm["graph"].as<bool>();
    }
    if (vm.count("graph_file")) {
      graph_file = vm["graph_file"].as<std::string>();
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
  if (graph) {
    if (graph_file == "") {
      graph_file = problem.head +".png"; 
    }
    auto start = std::chrono::high_resolution_clock::now();
    auto results = cppMCTShop(domain,problem,scorers[score_fun],R,plan_size,c,seed); 
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << "Time taken by planner: "
        << duration.count() << " microseconds" << endl;
    generate_graph(results.t[results.end].plan,domain,results.tasktree,results.ttRoot,graph_file);
  }
  else {
    auto start = std::chrono::high_resolution_clock::now();
    cppMCTShop(domain,problem,scorers[score_fun],R,plan_size,c,seed); 
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << "Time taken by planner: "
        << duration.count() << " microseconds" << endl;
  } 
  return EXIT_SUCCESS;
}
