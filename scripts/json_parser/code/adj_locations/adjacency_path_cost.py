"""
--------------------------------------------------------------------------
Purpose:
    Extract location adjacency from Semantic map "Saturn_2.6_3D_sm_v1.0.json"

Functions used from the Networkx Library:
    * all_pairs_shortest_path(saturn)
    * all_pairs_shortest_path_length(saturn)
    * single_source_shortest_path(graph, node)
    * all_pairs_dijkstra_path_length(graph, node)       # Adarsh's preference
    * single_source_dijkstra_path_length(graph, node)
    * (graph, node)
    * (graph, node)

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Last Updated:
    30 June  2023

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

# For easier reading of output
hrule = ("\n"+"-"*80+"\n")

filename = "Saturn_2.6_3D_sm_v1.0.json"
loc_list = []
data_list = [] 
connect_list = []
object_list = []
child_locations = []

# Read in this list of dictionaries and use the json.load() function.
try:
    with open(filename) as f:
        data = json.load(f)  # This loads the entire file as JSON
        # locations, connections, and objects
        for d in data:
            if d not in data_list:
                data_list.append(d)
        #print(hrule, "Data ==", data_list)

        # Now look at each 'locations'
        locations = data['locations']  # This is the list of location dictionaries
        for i, location in enumerate(locations):
            for l in location:
                if l not in loc_list:
                    loc_list.append(l)
        #print(hrule, "\tData['locations'] ==", loc_list)

        # Now look at each 'connections'
        connections = data['connections']
        for j, connection in enumerate(connections):
            for c in connection:
                if c not in connect_list:
                    connect_list.append(c)
        #print(hrule, "\tData['connection'] ==", connect_list)

        # Create the new dictionary but at this point, I think I'll use Loren's
            # output from his parser (Friday 30 June)
        new_dict = {}

        for item in connections:
            if 'connected_locations' in item:
                connected_locations_list = item['connected_locations']
                #print("\nNew connected locations list:", connected_locations_list)
                rooms = len(connected_locations_list)
                if 'loc' not in connected_locations_list:
                    if rooms == 1:
                        #print("\nSINGLE locations list:", connected_locations_list)
                        continue
                    connected_locations_key = connected_locations_list[0]
                    connected_locations_value = connected_locations_list[1]
                    new_dict[connected_locations_key] = connected_locations_value
                    if rooms == 3:
                        #print("\nTRIPLE connected locations list:", connected_locations_list)
                        connected_locations_value = connected_locations_list[2]
                        new_dict[connected_locations_key] = connected_locations_value
                    if rooms > 3:
                        print("\nWHOA!!!! connected locations list:", connected_locations_list)
                        ##connected_locations_value = connected_locations_list[2]
                        new_dict[connected_locations_key] = connected_locations_value
            else:
                connected_locations_value = []

        # Now look at each 'objects'
        objects = data['objects']
        for k, object in enumerate(objects):
            for o in object:
                if o not in object_list:
                    object_list.append(o)
        #print(hrule, "\tData['objects'] ==", object_list)

except (FileNotFoundError, json.JSONDecodeError) as e:
    print(f"An error occurred: {e}")

# Quick check of new dictionary items:
sorted_dict = dict(sorted(new_dict.items()))
#print(json.dumps(sorted_dict, indent = 4))

#----------------------------------- New Idea ------------------------------
# Loren already parsed the map with the graph. Trying with this output:
map = {"zones":["A4A","A4","A3","A2","A1","ccw","mcw","ccn","B7","crc","B5","B2","rrc","B1","B8","B3","B6","B9","B4","cce","C8","C7","C6","C5","C4","C3","C2","C1","llcn","D3","ca","E4","llc","E3","E2","E1","E5","D4","F4","F3","F2","F1","D2","D1","sga","G3","G2","G1","el","ew","H1","mce","buf","H2","H1A","scn","I4A","I3A","I2A","I1A","I4","I3","I2","I1","scw","J4","J3","J2","J1","K4","K3","K2","K1","scc","M3","L3","M2","L2","M1","L1","sce"],"graph":{"A4A":["A4"],"A4":["ccw","A4A"],"A3":["ccw"],"A2":["ccw"],"A1":["mcw"],"ccw":["B1","B2","A2","A3","A4","mcw","rrc","crc","ccn"],"mcw":["A1","el","ccw","cce","ca"],"ccn":["B8","B7","cce","ccw"],"B7":["ccn","crc"],"crc":["B6","B5","cce","B7","ccw"],"B5":["crc"],"B2":["ccw","B3"],"rrc":["B4","B3","cce","ccw"],"B1":["cce","ccw"],"B8":["ccn"],"B3":["rrc","B2"],"B6":["crc"],"B9":["cce"],"B4":["rrc"],"cce":["C2","C3","C4","C5","C6","C7","C8","B1","B9","rrc","crc","ccn","C1","mcw"],"C8":["cce","llcn"],"C7":["cce"],"C6":["cce"],"C5":["cce"],"C4":["cce"],"C3":["cce"],"C2":["cce"],"C1":["cce"],"llcn":["C8","scn","llc"],"D3":["ca"],"ca":["D4","D1","D2","D3","mcw"],"E4":["llc"],"llc":["buf","G1","G2","G3","F1","F2","F3","F4","E1","E2","E3","E5","E4","llcn","el"],"E3":["llc"],"E2":["llc"],"E1":["llc"],"E5":["llc"],"D4":["el","ca"],"F4":["llc"],"F3":["llc"],"F2":["llc"],"F1":["llc"],"D2":["ca"],"D1":["ca"],"sga":["ew"],"G3":["llc"],"G2":["llc"],"G1":["llc"],"el":["H1","D4","mcw","mce","llc"],"ew":["sga"],"H1":["mce","el","H1A"],"mce":["H1","el","scw","scc","sce"],"buf":["H2","llc"],"H2":["buf"],"H1A":["H1"],"scn":["llcn","sce","scw","scc"],"I4A":["I4"],"I3A":["I3"],"I2A":["I2"],"I1A":["I1"],"I4":["scw","I4A"],"I3":["scw","I3A"],"I2":["scw","I2A"],"I1":["scw","I1A"],"scw":["J1","J2","J3","J4","I1","I2","I3","I4","mce","scn"],"J4":["scw"],"J3":["scw"],"J2":["scw"],"J1":["scw"],"K4":["scc"],"K3":["scc"],"K2":["scc"],"K1":["scc"],"scc":["L1","L2","L3","K1","K2","K3","K4","mce","scn"],"M3":["sce"],"L3":["scc"],"M2":["sce"],"L2":["scc"],"M1":["sce"],"L1":["scc"],"sce":["M1","M2","M3","mce","scn"]},"rooms":["A4A","A4","A3","A2","A1","B7","B5","B2","B1","B8","B3","B6","B9","B4","C8","C7","C6","C5","C4","C3","C2","C1","D3","ca","E4","E3","E2","E1","E5","D4","F4","F3","F2","F1","D2","D1","sga","G3","G2","G1","H1","buf","H2","H1A","I4A","I3A","I2A","I1A","I4","I3","I2","I1","J4","J3","J2","J1","K4","K3","K2","K1","M3","L3","M2","L2","M1","L1"]}

#------------------------------- Graphs: Visualizations and Paths -------------------

saturn = networkx.Graph()
node_list = []

# For every key that I have in this data, that is going to be my node.
    # Then I iterate over each of these nodes. As I iterate over each node,
    # I access the values. In this case, the values are the edges-- the
    # connections I have between these nodes. Then, while I focus on one node
    # at a time, i iterate over each connection and add that edge
    # connection to my graph.

for node, connections in map["graph"].items():
    for connection in connections:
        saturn.add_edge(node, connection)
        if node not in node_list:
            node_list.append(node)

#print(node_list)

# We want to have a good repelling factor for the node visualization??
# To use path_graph(), we need the number of locations in this map.
numLoc = len(node_list)

# We don't need a lot of iterations to find the best layout. I could also
    # use coordinates to fix these nodes in place.
    # Default repel is 1/sqrt(numLoc). But this looks ugly.

default_k = 1/(numpy.sqrt(numLoc))
#print(default_k)

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

#-------------------------------------------------- Paths

# Testing only... randomize later.
print("Shortest path from A4A to L2:\n", networkx.dijkstra_path(saturn, 'A4A', 'L2'))



# If we want to automate our paths
source = random.choice(node_list)
target = random.choice(node_list)
if source == target:
    target = random.choice(node_list)

# Comment out the print statements for the final commit.
print(hrule, "If we want to automate our path choices:\nSource:", source, "\nTarget:", target)
print("\nDijkstra's Path:", networkx.dijkstra_path(saturn, source, target))

# Adarsh said unweighted and Clay said to assume uniform cost.
# This function assumes uniform cost:
print(hrule, "For ALL PAIRS path length using Dijkstra's Algorithm:")

adj_room_dict = dict(networkx.all_pairs_dijkstra_path_length(saturn,
                                                             weight = 'weight'))


# Comment out if no printing desired; limit is only to contrain printed output
count = 0
for s,a in adj_room_dict.items():
    print("\n{", s, ":", a, "\n}")
    count += 1
    if count > 10:
        break


# Now save this to a file:
with open('saved_adj_path_cost.json', 'w') as json_file:
    json.dump(adj_room_dict, json_file)


# ------------# TODO: Do we need these ideas? -----------------------

print(hrule, "\nIf we only care about the source {}, here is single_source_dijkstra_path_length:".format(source))
ssd = dict(networkx.single_source_dijkstra_path_length(saturn,
                                                 source,
                                                 weight = 'weight'))
print(ssd)


print(hrule, "If we only care about the source {}, here is all_pairs_shortest_paths:".format(source))
source_path = networkx.single_source_shortest_path(saturn, source)
count = 0
# Comment out if no printing desired; limit is only to contrain printed output
for s in source_path.items():
    print("  ", s)
    count += 1
    if count > 20:
        break

print(hrule, "If we only care about the target {}, here is all_pairs_shortest_paths:".format(target))
target_path = networkx.single_source_shortest_path(saturn, target)
# Comment out if no printing desired; limit is only to contrain printed output
count = 0
for s in target_path.items():
    print("  ", s)
    count += 1
    if count > 20:
        break

# Saving all pairs of all shortest paths (not using Dijkstra's Algorithm)
all_pairs_shortest_path = dict(networkx.all_pairs_shortest_path(saturn))

with open('saved_all_pairs_shortest_path.json', 'w') as json_file:
    json.dump(all_pairs_shortest_path, json_file)



# checking something: Does not use Dijkstra's 
testing = dict(networkx.all_pairs_shortest_path_length(saturn))
print(hrule, "All pairs shorest path length, but not using Dijkstra's:\n", testing)


