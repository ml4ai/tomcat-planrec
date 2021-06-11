#pragma once
#include <nlohmann/json.hpp>
#include <graphviz/gvc.h>
#include <string>

using json = nlohmann::ordered_json;

void set_property(Agnode_t *node,
                  std::string property_name,
                  std::string property_value) {
  agsafeset(node,
            const_cast<char *>(property_name.c_str()),
            const_cast<char *>(property_value.c_str()),
            const_cast<char *>(""));
}

void set_property(Agedge_t *edge,
                  std::string property_name,
                  std::string property_value) {
  agsafeset(edge,
            const_cast<char *>(property_name.c_str()),
            const_cast<char *>(property_value.c_str()),
            const_cast<char *>(""));
}

void set_property(Agraph_t *g,
                  int kind,
                  std::string property_name,
                  std::string property_value) {
  agattr(g,
         kind,
         const_cast<char *>(property_name.c_str()),
         const_cast<char *>(property_value.c_str()));
}

Agnode_t *add_node(Agraph_t *g, std::string node_name) {
  return agnode(g, const_cast<char *>(node_name.c_str()), 1);
}

int build_graph(Agraph_t *g, Agnode_t *n,json j,int count) {
  if (j["children"].empty()) {
    return count;
  }
  Agnode_t *m;
  Agedge_t *v;
  for (auto& e : j["children"]) {
    std::string tmp = std::to_string(count);
    m = add_node(g,tmp);
    set_property(m,"label",e["task"]);
    v = agedge(g,n,m,0,1);
    count++;
    count = build_graph(g,m,e,count);
  }
  return count;
}

void generate_graph_from_json(json j, std::string filename) {
  Agraph_t *g;
  Agnode_t *n;
  Agsym_t *a;
  GVC_t *gvc;
  gvc = gvContext();
  g = agopen(const_cast<char*>("g"), Agdirected,NULL);

  std::string tmp = std::to_string(0);

  n = add_node(g,tmp);
  set_property(n,"label",j["task"]);

  build_graph(g,n,j,1);

  gvLayout(gvc,g,"dot");
  gvRenderFilename(gvc,g,"png", const_cast<char*>(filename.c_str()));
  gvFreeLayout(gvc, g);
  agclose(g);
  gvFreeContext(gvc);
}




