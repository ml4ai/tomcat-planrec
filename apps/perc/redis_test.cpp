#include <sw/redis++/redis++.h>
#include <iostream>

using namespace sw::redis;

int main() {
  try {
    auto redis = Redis("tcp://127.0.0.1:6379");
    std::vector<std::pair<std::string,std::pair<std::string,std::string>>> xresults;
    redis.xrange("test_vic","-","+",5,std::back_inserter(xresults));
    for (auto x : xresults) {
      std::cout << x.first << " : " << x.second.first << x.second.second << std::endl;
    }
    //redis.flushall();
  } catch (const Error &e) {
    std::cout << "Failed : " << e.what() << std::endl;
  }
  return 0;
}
