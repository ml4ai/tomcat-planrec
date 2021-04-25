#include "simple_travel_example.h"

using namespace std;

int main(int argc, char* argv[]) {
    auto state1 = TravelState("state1");
    state1.loc["me"] = "home";
    state1.cash["me"] = 20;
    state1.owe["me"] = 0;
    state1.dist["home"]["park"] = 8;
    state1.dist["park"]["home"] = 8;

    // Declare operators
    Operators<TravelState> operators = {};
    operators["walk"] = walk;
    operators["ride_taxi"] = ride_taxi;
    operators["call_taxi"] = call_taxi;
    operators["pay_driver"] = pay_driver;

    cout << "Operators: ";
    print(operators);

    // Declare methods
    Methods<TravelState> methods = {};
    methods["travel"] = {travel_by_foot, travel_by_taxi};
    cout << "Methods: ";
    print(methods);

    Tasks tasks = {
        {Task("travel", Args({{"a", "me"}, {"x", "home"}, {"y", "park"}}))}};
    pyhop(state1, tasks, operators, methods);
    return EXIT_SUCCESS;
}
