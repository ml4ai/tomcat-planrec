#include "../../domains/pr_samples.h"
#include <math.h>
#include <stdlib.h>
#include <istream>
#include <boost/program_options.hpp>
#include <boost/json.hpp>
#include "util.h"
#include "cpphop/loader.h"
#include "cpphop/planlib_planrec.h"
#include "cpphop/grapher.h"
#include <chrono>
namespace po = boost::program_options;
namespace json = boost::json;

using namespace std;

int main(int argc, char* argv[]) {
  std::string planlib_file = "../domains/transport_planlib.json";
  std::string sample = "delivery_sample";
  int sample_size = 2;
  int pred = 3;
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("plan_lib,L",po::value<std::string>(),"Plan Library file, default = transport_planlib.json")
      ("sample,S",po::value<std::string>(),"Plan Rec sample (string), default = delivery_sample")
      ("sample_size,ss",po::value<int>(),"sample size for Plan Rec sample (int), default = 2")
      ("prediction_size,I",po::value<int>(),"Size of action prediction to make after plan recognition (int), default = 3")
    ;

    po::variables_map vm;        
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
      std::cout << desc << std::endl;
      return 0;
    }

    if (vm.count("plan_lib")) {
      planlib_file = vm["plan_lib"].as<std::string>();
    }

    if (vm.count("sample")) {
      sample = vm["sample"].as<std::string>();
    }
    
    if (vm.count("sample_size")) {
      sample_size = vm["sample_size"].as<int>();
    }

    if (vm.count("prediction_size")) {
      pred = vm["prediction_size"].as<int>();
    }
  }
  catch(std::exception& e) {
    std::cerr << "error: " << e.what() << "\n";
    return 1;
  }
  catch(...) {
    std::cerr << "Exception of unknown type!\n";
  }
  auto planlib = parse_file(planlib_file.c_str()); 
  auto first = pr_samples[sample].begin();
  auto last = pr_samples[sample].begin() + sample_size;
  std::vector<std::string> given_plan(first,last);
  std::vector<std::string> ground_truth(last,last + pred);

  auto start = std::chrono::high_resolution_clock::now();
  auto results = seek_explanation(planlib.as_object(),given_plan);
  auto stop = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
  cout << "Time taken by planrec: "
      << duration.count() << " microseconds" << endl;
  cout << "Ground Truth Actions (" << pred << ")" << endl;
  for (auto const& gt : ground_truth) {
    cout << gt << " ";
  }
  cout << endl;
  cout << endl;
  cout << "Predicted Actions (" << pred << ")" << endl;
  for (auto& r : results) {
    for (auto it = r.as_object()["plan"].as_array().begin() + sample_size; it != r.as_object()["plan"].as_array().begin() + sample_size + pred; it++) {
      cout << *it << " ";
    }
    cout << endl;
  }
  return EXIT_SUCCESS;
}
