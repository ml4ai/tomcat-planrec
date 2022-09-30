#include "../../domains/pr_samples.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include <boost/program_options.hpp>
#include <boost/json.hpp>
#include "cpphop/loader.h"
#include "cpphop/planlib_planrec.h"
#include "cpphop/grapher.h"
#include <chrono>
namespace po = boost::program_options;
namespace json = boost::json;

using namespace std;

int main(int argc, char* argv[]) {
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string plan_lib = "../domains/transport_planlib.json";
  std::string sample = "delivery_sample";
  int sample_size = 2;
  bool graph = false;
  std::string graph_file = "";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("plan_lib,L",po::value<std::string>(),"Plan Library file, default = transport_planlib.json")
      ("sample,S",po::value<std::string>(),"Plan Rec sample (string), default = delivery_sample")
      ("sample_size,ss",po::value<int>(),"sample size for Plan Rec sample (int), default = 2")
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

    if (vm.count("dom_file")) {
      dom_file = vm["dom_file"].as<std::string>();
    }

    if (vm.count("prob_file")) {
      prob_file = vm["prob_file"].as<std::string>();
    }

    if (vm.count("plan_lib")) {
      plan_lib = vm["plan_lib"].as<std::string>();
    }

    if (vm.count("sample")) {
      sample = vm["sample"].as<std::string>();
    }
    
    if (vm.count("sample_size")) {
      sample_size = vm["sample_size"].as<int>();
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
  auto first = pr_samples[sample].begin();
  auto last = pr_samples[sample].begin() + sample_size;
  std::vector<std::string> given_plan(first,last);
  if (graph) {
    if (graph_file == "") {
      graph_file = problem.head +".png"; 
    }
    auto start = std::chrono::high_resolution_clock::now();
    auto results = cppMCTSplanrec(domain,problem,given_plan,scorers[score_fun],R,plan_size,eps,successes,prob,seed); 
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << "Time taken by planner: "
        << duration.count() << " microseconds" << endl;
    generate_graph(results.t[results.end].plan,domain,results.tasktree,results.ttRoot,graph_file);
  }
  else {
    auto start = std::chrono::high_resolution_clock::now();
    cppMCTSplanrec(domain,problem,given_plan,scorers[score_fun],R,plan_size,eps,successes,prob,seed); 
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << "Time taken by planner: "
        << duration.count() << " microseconds" << endl;
  } 
  return EXIT_SUCCESS;
}
