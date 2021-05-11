#pragma once

#include <string>
#include <boost/graph/adjacency_list.hpp>
#include <boost/range/iterator_range.hpp>
#include "Node.hpp"
#include "util.h"

//adjacency_list<OutEdgeList, VertexList, Directed,
//                VertexProperties, EdgeProperties,
//                GraphProperties, EdgeList>
// Note: When setS or hash_setS is used as OutEdgeList, Boost Graph Library
//       gives memory problems on remove_vertex cal sometimes leading to
// segmentation faults. So changed it to vecS
class TreeData {
  public:
    Plans plans;
};


template <class State, class Selector>
using Tree = boost::adjacency_list<boost::vecS,
                              boost::vecS,
                              boost::bidirectionalS,
                              Node<State, Selector>,
                              boost::no_property,
                              TreeData>;

//Keeping these functions just in case we can fix them.
//For now, DO NOT USE THEM! They cause weird behaviors/segfaults
template <class State, class Selector>
auto get_successors(Tree<State,Selector> t,int i) {
    return boost::make_iterator_range(boost::adjacent_vertices(i, t));
}

template <class State, class Selector>
std::vector<int> get_successor_list(Tree<State,Selector> t,int i) {
    std::vector<int> successors = {};
    for (int successor : get_successors(t,i)) {
      if (successor != i) {
        successors.push_back(successor);
      }
    }
    return successors;
}

template <class State, class Selector>
auto get_predecessors(Tree<State,Selector> t, int i) {
  return boost::make_iterator_range(boost::inv_adjacent_vertices(i,t));
}

template <class State, class Selector>
std::vector<int> get_predecessor_list(Tree<State,Selector> t,int i) {
    std::vector<int> predecessors = {};
    for (int predecessor : get_predecessors(t,i)) {
      if (predecessor != i) {
        predecessors.push_back(predecessor);
      }
    }
    return predecessors;
}
