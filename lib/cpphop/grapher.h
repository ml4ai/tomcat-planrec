#pragma once
#include <graphviz/gvc.h>
#include <string>
#include "typedefs.h"

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
 
void  build_graph(Agraph_t *g, 
                  Agnode_t *n, 
                  DomainDef& domain, 
                  TaskTree& t,
                  int w,
                  std::unordered_map<std::string,std::string>& action_map) {
  std::string tmp = std::to_string(w);
  n = add_node(g,tmp);
  set_property(n,"label",t[w].token);
  if (domain.actions.contains(t[w].task)) {
    set_property(n,"shape","rectangle");
    set_property(n,"color","blue");
    action_map[t[w].token] = tmp;
  }
  for (int i = t[w].children.size() - 1; i >= 0; i--) {
    Agnode_t *m;
    build_graph(g,m,domain,t,t[w].children[i],action_map);
    std::string ctmp = std::to_string(t[w].children[i]);
    m = add_node(g,ctmp);
    if (m != NULL) {
      Agedge_t *e;
      e = agedge(g,n,m,0,1);
      set_property(e,"style","dotted");
    }
    for (auto& o : t[t[w].children[i]].outgoing) {
      Agnode_t *u;
      Agedge_t *p;
      std::string otmp = std::to_string(o);
      u = add_node(g,otmp);
      p = agedge(g,m,u,0,1);
      set_property(p,"color","green");
    }
  }
  return;
}

void generate_graph(std::vector<std::string>& plan,DomainDef& domain, TaskTree& t, int root, std::string filename) {
  Agraph_t *g;
  Agnode_t *n;
  GVC_t *gvc;
  gvc = gvContext();
  g = agopen(const_cast<char*>("g"), Agdirected,NULL);
  std::unordered_map<std::string,std::string> action_map;
  build_graph(g,n,domain,t,root,action_map);
  for (int i = 1; i < plan.size(); i++) {
    Agnode_t *v;
    Agnode_t *w;
    Agedge_t *e;
    v = add_node(g,action_map[plan[i-1]]);
    w = add_node(g,action_map[plan[i]]);
    e = agedge(g,v,w,0,1);
    set_property(e,"color","red");
  }
  gvLayout(gvc,g,"dot");
  gvRenderFilename(gvc,g,"png", const_cast<char*>(filename.c_str()));
  gvFreeLayout(gvc, g);
  agclose(g);
  gvFreeContext(gvc);
}




