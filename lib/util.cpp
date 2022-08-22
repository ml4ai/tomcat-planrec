#include <vector>
#include <random>

int sample_method(std::vector<int> mds, std::vector<double> wts, int seed) {
    std::mt19937 gen(seed);
    std::discrete_distribution<int> dist(wts.begin(), wts.end());
    int s = dist(gen);
    return mds[s];
}

int sample_method(std::vector<int> mds, std::vector<double> wts) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::discrete_distribution<int> dist(wts.begin(), wts.end());
    int s = dist(gen);
    return mds[s];
}
