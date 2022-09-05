"""
Author: Salena Torres Ashton
Created: 17 August 2022
Purpose: Markov Chain for Domain Definition of work done in the spring
regarding the intention of players given their trigram utterance and/or given
the actions taken during, before and after question utterances.

Limitations: Data from patterns are from 12 video observations but patterns of
transition of all utterances are only from observation 638. This WILL limit the
methods, abstract tasks, and action definitions for the hddl domain.
"""




import numpy

hrule = ("\n" + "-"*60 + "\n")

##### TOY PROBLEM FOR CRITICAL WAKE Player intention  #####

# Current state indicates initial task is 55% likely to be task 9
# (clarifyCriticalLocation) for abstract task *CriticalWake 

toyI = numpy.matrix([[0.55, 0.44, 0]])

# Transition Matrix of Toyed problem for Critical Wake
toyT = numpy.matrix([[0.1, 0.9, 0],
               [0.4, 0, 0.6],
               [0.1, 0.4, 0.5]])

print("Toy T:", toyT)


for i in range(0, 100):
    #print("toyI:", toyI)
    prob = toyI * toyT
    #print("prob:", prob)
    final = prob
    #print("final:", final)
    toyI = prob
    #print("New toyI:", toyI)
    #print(hrule)

print("New toyI:", toyI, hrule)

# The data suggest that the probability of starting in 9, 8, or 4 are
# respectively 0.5, 0.33 or 0.16.
# See bottom of file for definitions of these task numbers
print("[[clarCritLoc, reqDest, askLocTeammate, wakeCrit, clarLoc]]\n\n")
I = numpy.matrix([[0.55, 0.33, 0.17, 0, 0]])

T = numpy.matrix([[0, 1, 0, 0, 0], # clarifyCriticalLocation
            [0.2, 0, 0, 0.2, 0.6], # requestDestination
            [0, 1, 0, 0, 0],       # askLocationTeammate
            [0, 0, 0, 1, 0],       # wakeCritical
            [0, 0.5, 0, 0.3, 0.2]])  # clarifyLocation

print("Data-driven Domain Definition of Critical Wake\n\nT:", T)
print(hrule, "Initial State:\n\n", I)

for i in range(0, 10):
    print("i:", i)
    prob = I * T
    final = prob
    I = prob
    print("New I:", I)
    print(hrule)

print("[[clarCritLoc, reqDest, askLocTeammate, wakeCrit, clarLoc]]\n\n")

"""
Description of Tasks that create the method "Critical Wake"

Task 9: clarifyCriticalLocation
Task 8: requestDestination
Task 4: askLocationTeammate
Task 18: wakeCritical
Task 5: clarifyLocation (of anything, not just victims)
"""
