#include <sw/redis++/redis++.h>
#include <iostream>

using namespace sw::redis;

int main() {
  try {
    auto redis = Redis("tcp://127.0.0.1:6379");
    std::vector<std::pair<std::string,std::vector<std::pair<std::string,std::string>>>> xresults;
    redis.xrange("fov","-","+",50,std::back_inserter(xresults));
    for (auto x : xresults) {
      std::cout << std::stoi(x.first) << " : " << std::endl;
      for ( auto y : x.second ) {
        std::cout << y.first << " " << y.second << std::endl;
      }
    }
  } catch (const Error &e) {
    std::cout << "Failed : " << e.what() << std::endl;
  }
  return 0;
}
