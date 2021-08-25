#include <queue>
#include "util.h"

int shortest_path_BFS(std::unordered_map<std::string,std::vector<std::string>> g, std::string src, std::string dest) {
  std::queue<std::string> Q;
  std::vector<std::string> visited;
  std::unordered_map<std::string,int> dist_from_src;
  dist_from_src[src] = 0;
  visited.push_back(src);
  Q.push(src);
  while(!Q.empty()) {
    std::string v = Q.front();
    Q.pop();
    if (v == dest) {
      return dist_from_src[v];
    }
    for (auto w : g[v]) {
      if (!in(w,visited)) {
        visited.push_back(w);
        dist_from_src[w] = dist_from_src[v] + 1;
        Q.push(w);
      } 
    }
  }
  return -1;
}
