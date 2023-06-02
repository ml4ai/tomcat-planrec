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
  int time_limit = 1000;
  int r = 5;
  double c = sqrt(2.0);
  int seed = 2022;
  int trials = 10;
  std::string dom_file = "../domains/transport_domain.hddl";
  std::string prob_file = "../domains/transport_problem.hddl";
  std::string score_fun = "delivery_one";
  std::string redis_address = "";
  std::string data_file = "eval.csv";
  try {
    po::options_description desc("Allowed options");
    desc.add_options()
      ("help,h", "produce help message")
      ("time_limit,T", po::value<int>(), "Time limit (in milliseconds) allowed for each search action (int), default = 1000")
      ("simulations,r", po::value<int>(), "Number of simulations per resource cycle (int), default = 5")
      ("exp_param,c",po::value<double>(),"The exploration parameter for the planner (double), default = sqrt(2)")
      ("dom_file,D", po::value<std::string>(),"domain file (string), default = transport_domain.hddl")
      ("prob_file,P",po::value<std::string>(),"problem file (string), default = transport_problem.hddl")
      ("score_fun,F",po::value<std::string>(),"name of score function (string), default = delivery_one")
      ("seed,s", po::value<int>(),"Random Seed (int)")
      ("trials,t",po::value<int>(),"Number of trials (with different seeds) per eval cycle (int), default = 10")
      ("redis_address,a",po::value<std::string>(), "Address to redis server, default = (none, no connection)")
      ("data_file,o",po::value<std::string>(),"file name for eval data (string), default = eval.csv")
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

    if (vm.count("seed")) {
      seed = vm["seed"].as<int>();
    }

    if (vm.count("trials")) {
      trials = vm["trials"].as<int>();
    }

    if (vm.count("redis_address")) {
      redis_address = vm["redis_address"].as<std::string>();
    }

    if (vm.count("data_file")) {
      data_file = vm["data_file"].as<std::string>();
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
    std::vector<double> observations;
    std::vector<double> horizon;
    std::vector<double> num_trials;
    std::vector<double> avg_accs;
    std::vector<double> ob_status;
    Redis_Connect* rc = Redis_Connect::getInstance(redis_address);
    std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> act_results;
    std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> exp_results;
    rc->redis.xrange("actions","-","+",std::back_inserter(act_results));
    rc->redis.xrange("explanations","-","+",std::back_inserter(exp_results));
    int i = 1;
    std::vector<int> times;
    std::vector<std::string> actions;
    for (auto ar : act_results) {
      times.push_back(std::stoi(ar.first));
      for (auto a : ar.second) {
        actions.push_back(a.second);
      }
    }
    for (auto ex : exp_results) {
      for (auto ey : ex.second) {
        json::value j = json::parse(ey.second);
        TaskGraph taskgraph = json::value_to<TaskGraph>(j.as_object()["taskgraph"]);
        std::unordered_map<std::string, std::vector<std::string>> 
          facts = json::value_to<std::unordered_map<std::string, std::vector<std::string>>>(j.as_object()["state"]);
        std::vector<std::string> plan = json::value_to<std::vector<std::string>>(j.as_object()["plan"]);
        for (int j = 0; j < plan.size(); j++) {
          bool match = true;
          for (int k = 0; k < j + 1; k++) {
            if (plan[k].find(actions[k]) == std::string::npos) {
              match = false;
              break;
            }
          }
          observations.push_back(i);
          horizon.push_back(j + 1);
          num_trials.push_back(trials);
          ob_status.push_back(2);
          if (match) {
            avg_accs.push_back(1);
          }
          else {
            avg_accs.push_back(0);
          }
          std::cout << "Data Saved for observations " << i << ", horizon " << j + 1 << std::endl;
        }
        std::vector<int> c_t;
        for (int j = plan.size(); j < times.size(); j++) {
          c_t.push_back(times[j]); 
          double acc = 0.0;
          for (int k = 0; k < trials; k++) {
            auto psol = cppMCTSeval(domain,
                                    problem,
                                    scorers[score_fun],
                                    taskgraph,
                                    facts,
                                    c_t,
                                    time_limit,
                                    r,
                                    c,
                                    seed,
                                    redis_address);
            std::vector<std::string> pred = merge_vec(plan,psol);
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
          observations.push_back(i);
          horizon.push_back(j + 1);
          num_trials.push_back(trials);
          if (i == j + 1) {
            ob_status.push_back(1);
          }
          else {
            ob_status.push_back(0);
          }
          avg_accs.push_back(acc);
          std::cout << "Data Saved for observations " << i << ", horizon " << j + 1 << std::endl;
        }
        i++;
      }
    }
    std::vector<std::pair<std::string, std::vector<double>>> 
      dataset = {{"Observations",observations},
                 {"Horizon", horizon},
                 {"Trials", num_trials},
                 {"Status", ob_status},
                 {"Average Accuracy", avg_accs}
                };
    write_csv(data_file,dataset);
    std::cout << "Evaluation Completed" << std::endl;
  }
  else {
    std::cout << "No redis server address given, shutting down!" << std::endl; 
  }
  return EXIT_SUCCESS;
}
