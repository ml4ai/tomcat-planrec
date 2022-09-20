#include "domains/simple_travel.h"
#include <chrono>

using namespace std;

int main(int argc, char* argv[]) {
    auto state1 = TravelState("state1");
    state1.loc["me"] = "home";
    state1.cash["me"] = 20;
    state1.owe["me"] = 0;
    state1.dist["home"]["park"] = 1;
    state1.dist["park"]["home"] = 1;
    auto domain = TravelDomain();

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}),{"a","x","y"},{"me"})}};
    auto start = std::chrono::high_resolution_clock::now();
    cppMCTShop(state1, tasks, domain, 30, -1, 0.4, 4021, 10);
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << "Time taken by planner: "
         << duration.count() << " microseconds" << endl;
    return EXIT_SUCCESS;
}
