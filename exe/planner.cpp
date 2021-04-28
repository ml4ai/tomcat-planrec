#include "simple_travel_example.h"

using namespace std;

int main(int argc, char* argv[]) {
    auto state1 = TravelState();
    state1.loc["me"] = "home";
    state1.cash["me"] = 20;
    state1.owe["me"] = 0;
    state1.dist["home"]["park"] = 1;
    state1.dist["park"]["home"] = 1;
    auto domain = TravelDomain();

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}))}};
    cpphopDFS(state1, tasks, domain);
    return EXIT_SUCCESS;
}
