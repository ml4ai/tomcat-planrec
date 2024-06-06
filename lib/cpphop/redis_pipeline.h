#pragma once

#include "../Redis_Connect.h"
#include "../typedefs.h"

using Attrs = std::vector<std::pair<std::string,std::string>>;
using Item = std::pair<std::string, std::optional<Attrs>>;
using ItemStream = std::vector<Item>;

void update_actions(std::string const& redis_address,
                    std::vector<std::pair<int, std::string>>& actions) {
  Redis_Connect* rc = Redis_Connect::getInstance(redis_address);
  std::string oldest;
  if (actions.empty()) {
    oldest = "0";
  }
  else {
    oldest = std::to_string(actions.back().first);
  }
  std::unordered_map<std::string,ItemStream> result;
  rc->redis.xread("actions",oldest,std::inserter(result,result.end()));
  if (result["actions"].empty()) {
    std::pair<int,std::string> p;
    p.first = -1;
    p.second = "__STOP__";
    actions.push_back(p);
  }
  for (auto const& x : result["actions"]) {
    Attrs attrs = x.second.value();
    for (auto const& y : attrs) {
      std::pair<int,std::string> p;
      p.first = std::stoi(x.first);
      p.second = y.second;
      actions.push_back(p);
    }
  }
}

void upload_plan_explanation(std::string const& redis_address,
                             TaskTree& tasktree,
                             std::vector<int> treeRoots,
                             std::vector<std::string>& plan,
                             std::vector<std::string>& acts,
                             TaskGraph& taskgraph,
                             std::unordered_map<std::string, std::unordered_set<std::string>> facts) {
  //Serialize task tree and current plan
  json::object obj;
  obj["treeRoots"] = json::value_from(treeRoots);
  obj["tasktree"] = json::value_from(tasktree);
  obj["plan"] = json::value_from(plan);
  obj["actions"] = json::value_from(acts);
  obj["taskgraph"] = json::value_from(taskgraph);
  obj["state"] = json::value_from(facts);
  std::string s = json::serialize(obj);
  Redis_Connect* rc = Redis_Connect::getInstance(redis_address);
  rc->redis.xadd("explanations","*",{std::make_pair("explanation",s)});
}
