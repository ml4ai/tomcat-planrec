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
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("plan_lib,L",po::value<std::string>(),"Plan Library file, default = transport_planlib.json")
      ("sample,S",po::value<std::string>(),"Plan Rec sample (string), default = delivery_sample")
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
  double trials = 0;
  double avg_c = 0;
  double avg_p = 0;
  for (int i = 1; i < pr_samples[sample].size(); i++) {
    trials++;
    auto last = pr_samples[sample].begin() + i;
    std::vector<std::string> given_plan(first,last);
    std::string ground_truth = pr_samples[sample][i];
    auto results = seek_explanation(planlib.as_object(),given_plan);
    double m_count = 0;  
    double r_count = 0;
    for (auto& r : results) {
      r_count++;
      if (r.as_object()["plan"].as_array()[i].as_string().find(ground_truth) != json::string::npos) {
        m_count++; 
      }
    }
    double c = m_count/r_count;
    double p = 1.0/m_count;
    cout << "Observations: " << given_plan.size() << ", ";
    cout << m_count << " positive matches out of " << r_count << " results, correctness: ";
    cout << c << ", precision: " << p << endl;
    avg_c += c;
    avg_p += p;
  }
  cout << endl;
  cout << "Average Correctness: " << avg_c/trials << endl; 
  cout << "Average Precision: " << avg_p/trials << endl;
  return EXIT_SUCCESS;
}
