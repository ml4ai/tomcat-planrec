"""
--------------------------------------------------------------------------
Purpose:
    Extract location adjacency from Semantic map "Saturn_2.6_3D_sm_v1.0.json"

Functions used from the Networkx Library:
    * all_pairs_dijkstra_path_length(graph, node)

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Last Updated:
    3 July 2023

Affiliation:
    Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
    ASIST Program (DARPA)
    Adarsh Pyarelal, PI
    School of Information;  University of Arizona

--------------------------------------------------------------------------
"""

import json
from pprint import pprint
import random
import networkx
import numpy
import matplotlib.pyplot as plot

# This graph output is from the semantic map "Saturn_2.6_3D_sm_v1.0.json"

map = {"zones":["A4A","A4","A3","A2","A1","ccw","mcw","ccn","B7","crc","B5","B2","rrc","B1","B8","B3","B6","B9","B4","cce","C8","C7","C6","C5","C4","C3","C2","C1","llcn","D3","ca","E4","llc","E3","E2","E1","E5","D4","F4","F3","F2","F1","D2","D1","sga","G3","G2","G1","el","ew","H1","mce","buf","H2","H1A","scn","I4A","I3A","I2A","I1A","I4","I3","I2","I1","scw","J4","J3","J2","J1","K4","K3","K2","K1","scc","M3","L3","M2","L2","M1","L1","sce"],"graph":{"A4A":["A4"],"A4":["ccw","A4A"],"A3":["ccw"],"A2":["ccw"],"A1":["mcw"],"ccw":["B1","B2","A2","A3","A4","mcw","rrc","crc","ccn"],"mcw":["A1","el","ccw","cce","ca"],"ccn":["B8","B7","cce","ccw"],"B7":["ccn","crc"],"crc":["B6","B5","cce","B7","ccw"],"B5":["crc"],"B2":["ccw","B3"],"rrc":["B4","B3","cce","ccw"],"B1":["cce","ccw"],"B8":["ccn"],"B3":["rrc","B2"],"B6":["crc"],"B9":["cce"],"B4":["rrc"],"cce":["C2","C3","C4","C5","C6","C7","C8","B1","B9","rrc","crc","ccn","C1","mcw"],"C8":["cce","llcn"],"C7":["cce"],"C6":["cce"],"C5":["cce"],"C4":["cce"],"C3":["cce"],"C2":["cce"],"C1":["cce"],"llcn":["C8","scn","llc"],"D3":["ca"],"ca":["D4","D1","D2","D3","mcw"],"E4":["llc"],"llc":["buf","G1","G2","G3","F1","F2","F3","F4","E1","E2","E3","E5","E4","llcn","el"],"E3":["llc"],"E2":["llc"],"E1":["llc"],"E5":["llc"],"D4":["el","ca"],"F4":["llc"],"F3":["llc"],"F2":["llc"],"F1":["llc"],"D2":["ca"],"D1":["ca"],"sga":["ew"],"G3":["llc"],"G2":["llc"],"G1":["llc"],"el":["H1","D4","mcw","mce","llc"],"ew":["sga"],"H1":["mce","el","H1A"],"mce":["H1","el","scw","scc","sce"],"buf":["H2","llc"],"H2":["buf"],"H1A":["H1"],"scn":["llcn","sce","scw","scc"],"I4A":["I4"],"I3A":["I3"],"I2A":["I2"],"I1A":["I1"],"I4":["scw","I4A"],"I3":["scw","I3A"],"I2":["scw","I2A"],"I1":["scw","I1A"],"scw":["J1","J2","J3","J4","I1","I2","I3","I4","mce","scn"],"J4":["scw"],"J3":["scw"],"J2":["scw"],"J1":["scw"],"K4":["scc"],"K3":["scc"],"K2":["scc"],"K1":["scc"],"scc":["L1","L2","L3","K1","K2","K3","K4","mce","scn"],"M3":["sce"],"L3":["scc"],"M2":["sce"],"L2":["scc"],"M1":["sce"],"L1":["scc"],"sce":["M1","M2","M3","mce","scn"]},"rooms":["A4A","A4","A3","A2","A1","B7","B5","B2","B1","B8","B3","B6","B9","B4","C8","C7","C6","C5","C4","C3","C2","C1","D3","ca","E4","E3","E2","E1","E5","D4","F4","F3","F2","F1","D2","D1","sga","G3","G2","G1","H1","buf","H2","H1A","I4A","I3A","I2A","I1A","I4","I3","I2","I1","J4","J3","J2","J1","K4","K3","K2","K1","M3","L3","M2","L2","M1","L1"]}

saturn = networkx.Graph()

# We want to have a good repelling factor for the node visualization.
node_list = []

for node, connections in map["graph"].items():
    for connection in connections:
        saturn.add_edge(node, connection)
        if node not in node_list:
            node_list.append(node)

numLoc = len(node_list)

# Default node repel is 1/sqrt(numLoc), which is k = 0.111 and  not visually appealing. 
# The current, hard-coded repel factor is k = 1.
default_k = 1/(numpy.sqrt(numLoc))
spring_layout = networkx.spring_layout(saturn,
                                       iterations = 100,
                                       k = 1,
                                       seed = 123)
networkx.draw(saturn,
              pos = spring_layout,
              with_labels = True,
              node_color = 'skyblue',
              node_size = 400,
              arrows = True)
plot.figure(figsize=(50, 50))
#plot.show()

# Default value of weight = 1. This function was chosen so that variable
    # weights can be implemented in the future. 
#print(hrule, "For ALL PAIRS path length using Dijkstra's Algorithm:")

adj_room_dict = dict(networkx.all_pairs_dijkstra_path_length(saturn,
                                                             weight = 'weight'))

# Save to file:
with open('saved_adj_path_cost.json', 'w') as json_file:
    json.dump(adj_room_dict, json_file)

