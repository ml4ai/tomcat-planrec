'''
TODO: See line 140

Salena Ashton
Beginning functions for extractions. This is part of my learning process for
NLP studies during the summer (on my own time) and for ToMCAT applications.
Most of these functions, for now, are just for learning but the
verb/noun/modifier extractions will eventually be helpful for tomcat. 

Right now they are elementary since I am learning NLP.

'''

# feature functions intro

def ends_iner(token):
    return 1 if token.endswith("er") else 0



##### ##### ##### ##### ##### ##### ##### 
def getVowels(token):
    vowel = ["a", "e", "i", "o", "u", "y"]
    token2 = []
    for i in token:
        i.lower()
        if i in vowel:
            token2.append(i)

    return token2

##### ##### ##### ##### ##### ##### 

def startsWith(token):
    return token[0]

##### ##### ##### ##### ##### ##### 

def getLabels(myLabel):

    def getVerb(label):
        verb = ""

        for i in label:
            if i.islower():
                verb = verb + i
                # third para to have replace only once!
                label = label.replace(i, "", 1)
            else:
                print("\nFrom getVerb():\n", verb)
                return verb, label

    def getNoun(label):
        # remove capital letter for noun:
        noun = label[0].lower()
        label = label.replace(label[0], "", 1)

        for i in label:
            if i.islower():
                noun = noun + i
                label = label.replace(i, "", 1)
            else:
                print("\nFrom getNoun():\n", noun)
                return noun, label


    def getModifier(label):
        # remove capital letter for noun, make it lower and attach it to grab
        # modifier:
        modifier = label[0].lower()
        label = label.replace(label[0], "", 1)

        # Since we don't have a break for uppers, use length:
        size = len(label)
        count = 0

        for i in label:
            if count <= size:
                modifier = modifier + i
                label = label.replace(i, "", 1)
                size -= 1
                count += 1
            else:
                modifier = modifier + i
                label = label.replace(i, "", 1)
                print("\nFrom geModifier():\n", modifier)
                return modifier


    myVerb = ""
    myNoun = ""
    myMod = ""

    myVerb, myLabel = getVerb(myLabel)
    myNoun, myLabel = getNoun(myLabel)
    myModifier = getModifier(myLabel)

    print("\n\n", "="*50, "\nVerb:", myVerb, "\nNoun:", myNoun, "\nModifier:", myModifier)
    return myVerb, myNoun, myModifier
    ##### ##### ##### ##### ##### ##### 

#############################################
# Now use this for the data
import pandas
import numpy
import requests
import time

#Read in Data
rawData = pandas.read_csv("../data/causalLabels.csv")
print("Shape of data:", rawData.shape)
print("Type of data:", type(rawData))

pandaLabels = rawData["causalLabels"] + ", " + rawData["questionLabels"].astype(str)
print("Shape of data:", pandaLabels.shape)
print("Type of data:", type(pandaLabels))



'''
allLabels = []
print("type:", type(allLabels))
print(len(allLabels))
time.sleep(3)

allLabels = allLabels.append(rawData["causalLabel"])
print("type:", type(allLabels))
print(len(allLabels))
time.sleep(3)

allLabels = allLabels.append(rawData["questionLabel"])
print("type:", type(allLabels))
print(len(allLabels))
time.sleep(3)

allLabels = allLabels.append(rawData["effectLabel"])
print("type:", type(allLabels))
print(len(allLabels))
time.sleep(3)
'''

# get rid of nans and nulls:
#allLabels = [x for x in allLabels if str(x) == x]




'''
TODO:
I need to get rid of the nans and nulls because  it is not working for the
listing of nouns or verbs. The modifiers do work, however.

The point will be to have a list (not a set) of words from the getLabels()
function.
'''

##### ##### ##### ##### ##### ##### ##### ##### #####

# make verb, noun, and modifier lists from dataframe:

allNouns = []
allVerbs = []
allModifiers = []

for l in allLabels:
    token = str(l)
    v, n, m = getLabels(token)
    allVerbs.append(v)
    allNouns.append(n)
    allModifiers.append(m)

for p in allVerbs: 
    print("\n", "="*30, "All Verbs:\n", "-"*30, allVerbs)

for p in allNouns:
    print("\n", "="*30, "All Nouns:\n", "-"*30, allNouns)

for p in allModifiers:
    print("\n", "="*30, "All Modifiers:\n", "-"*30, allModifiers)







##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 
##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 
### TEST CODE ###

testLabel = "plantCornSweet"
testLabelList = ["plantCornSweet", "eatMeatLess", "drinkWaterDaily"]

getLabels(testLabel)

testv = []
testn = []
testm = []

for l in testLabelList:
    token = str(l)
    v, n, m = getLabels(token)
    print(v, n, "and", m)
    testv.append(v)
    testn.append(n)
    testm.append(m)

#print("My test lists:\n", testv, "\n", testn, "\n", testm)

print("\n", "="*30, "testLabelList:\n", testLabelList)
print("\n", "="*30, "All Labels:\n", allLabels[0:3])
print("\n", "="*30, "All Labels:\n", allLabels[0:3])


'''
## I'm not sure if I need this block anymore.

name = "Salena"
myList = ["student", "learner", "doer", "human"]
print(ends_iner(name))
for i in myList:
    print(ends_iner(i))

print(getVowels(name))
print(startsWith(name))
'''
##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 
##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 

def resolveRedundancies(verb, noun, mod, t1, t2, t3):

    vn = []
    for i in verb:
        for j in noun:
            if i == j:
                vn.append(i)

    print("\n\n\n", "-"*30, t1, "and", t2, "Redundancy List:\n")
    print(vn)


    nm = []
    for i in noun:
        for j in mod:
            if i == j:
                nm.append(i)

    print("\n\n\n", "-"*30, t2, "and", t3, "Redundancy List:\n")
    print(nm)


    vm = []
    for i in verb:
        for j in mod:
            if i == j:
                vm.append(i)

    print("\n\n\n", "-"*30, t1, "and", t3, "Redundancy List:\n")
    print(vm)



    all = []
    for i in vn:
        for j in nm:
            if i == j:
                all.append(i)

    print("\n\n\n", "-"*30, "All Redundancy List:\n")
    print(vm)
    print("These are the problem words-- no surprise.\n")

##### ##### ##### ##### ##### ##### ##### ##### #####

