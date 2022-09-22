#pragma once
#include <graphviz/gvc.h>
#include <string>

using json = nlohmann::json;

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

void build_graph(Agraph_t *g, Agnode_t *n, DomainDef& domain, TaskTree& t,int w) {
  std::string tmp = std::to_string(w);
  n = add_node(g,tmp);
  set_property(n,"label",t[w].token);
  if (domain.actions.contains(t[w].task)) {
    set_property(n,"shape","rectangle");
    set_property(n,"color","blue");
  }
  for (auto& e : t[w].children) {
    Agnode_t *m;
    build_graph(g,m,domain,t,e);
    agedge(g,n,m,0,1);
  }
  return;
}

void generate_graph(DomainDef& domain, TaskTree&, int root, std::string filename) {
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




