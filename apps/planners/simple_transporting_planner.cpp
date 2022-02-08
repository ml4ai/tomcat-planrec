#include "domains/simple_transporting.h"

using namespace std;

int main(int argc, char* argv[]) {
    auto state1 = TransState("state1");

    state1.t_loc["t1"] = "home";
    state1.p_loc["p1"] = "l1";
    state1.t_res["t1"] = "n";
    state1.t_load["t1"] = "e";

    auto domain = TransDomain();

    auto selector = TransSelector();

    Tasks tasks = {
        {Task("transport", Args({{"t", "t1"}, {"p", "p1"}, {"x", "l1"}, {"y", "l2"}}),{"t", "p", "x","y"},{"t", "p"})}};
    cpphopDFS(state1, tasks, domain, selector);
    return EXIT_SUCCESS;
}
