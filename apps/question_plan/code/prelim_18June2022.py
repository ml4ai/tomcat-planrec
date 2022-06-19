'''
Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 19 June 2022
Last Updated: 19 June 2022

Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
Planning Work Group
Adarsh Pyarelal, Head PI and Clayton T. Morrison, Co-PI
School of Information, University of Arizona

All code written by Salena Ashton and will be uploaded to the
    tomcat-planrec GitHub Repositiory

TODO:As of 19 June 2022
    * Convert date time to timestamp integer
    * Verify full meaning of 'raw text' before uploading data file
    * 



'''
### Horizontal ruling for visual ease in reading output.

hrule = ("\n" + " - "*30 + "\n")
Hrule = ("\n" + " = "*30 + "\n")
print(hrule)
print(Hrule)
###################################################################

import sys
import numpy
import pandas
import requests
import time
import datetime


rawData = pandas.read_csv("../data/doNotCommit_Cleaned.csv")
# If not in csv format, use read_json(), read_html(), read_sql_table()
print(type(rawData))


# EXAMINE THE DATA
print("Len() of data:", len(rawData))
print("Shape of data:", rawData.shape)

# Get rid of null values
print("Shape of data before cleaning out cause verb nulls:", rawData.shape)
rawData = rawData[rawData["obsNum"].notnull()]
print("Shape of data AFTER cleaning out nulls:", rawData.shape)
print(Hrule)


pandas.set_option('display.max_rows', 40)
pandas.set_option('display.max_columns', 22)
pandas.set_option('display.width', 150)
pandas.set_option('display.colheader_justify', 'center')
pandas.set_option('display.precision', 1) # decimal place

### Subset dataframe to focus on conditional probabilities of labels
data = rawData[["regular", "critical", "score", "timeStart", "timeEnd",
"question_verbatim", "htn", "abstractLabel", "causeLabel", "questionLabel",
"effectLabel", "qWord", "qPhrase", "auxVerb", "actionVerb"]]

print("From line 68: Head of Subset Data:\n", data.head())
print(hrule, "From line 69: Shape of data:", data.shape, hrule)
###################################################################
### Getting to know the Data:
#print(hrule, "\nData info():", data.info())

### Not as helpful for my research question 
#print(hrule, "Describe Data:\n", data.describe(), "\n")

### Describe using a parameter and numpy:
#print(hrule, "Describe Data with Parameter:\n", data.describe(include=object))

### Print data types of columns:
#print(hrule, "Data Types of Each Column:", data.dtypes)

### Convert datetime to integer timestamp. Since the mission progresses from 900
    ### start time and ends at 000 seconds, and since players refer to time in
    ### terms of "time left," I have reflected this in the data format.
### Change object datatypes to floats, then convert to time integers
'''
data["timeStart"] = pandas.to_datetime(data["timeStart"])
print(hrule, "Data Types of Each Column:", data.dtypes)

### Remove dates and then convert to seconds
data["timeStart"] = pandas.Series([val.time() for val in data["timeStart"]])

tempCol = []

for i in data["timeStart"]:
    print(i, "is START data type:", type(i))
    time = str(i)
    print("I is now a :", type(i), "and time is now:", type(time))
    time = time[:-3]
    print("after removing the last three chars, time is now:", time)
    date_time = datetime.datetime.strptime(time, "%M:%S")
    a_timedelta = date_time - datetime.datetime(1900, 1, 1)
    seconds = a_timedelta.total_seconds()
    print(seconds, "should be a float")
    print(i, "should be hhmmss")
    print(seconds, "again, but should now be a string of ss.00")# yes
    seconds = int(seconds)
    print(seconds, "again, but should now be an integer of ss.00")# yes
    tempCol.append(seconds)
    print(hrule)


'''

def convert_datetime_integer(column):

    column = pandas.to_datetime(column)
#    print(hrule, "Data Types of Each Column:", data.dtypes)
    ### Remove dates and then convert to seconds
    column = pandas.Series([val.time() for val in column])
    tempCol = []

    for i in column:
#        print(i, "is START data type:", type(i))
        time = str(i)
#        print("I is now a :", type(i), "and time is now:", type(time))
        time = time[:-3]
#        print("after removing the last three chars, time is now:", time)
        date_time = datetime.datetime.strptime(time, "%M:%S")
        a_timedelta = date_time - datetime.datetime(1900, 1, 1)
        seconds = a_timedelta.total_seconds()
#        print(seconds, "should be a float")
#        print(i, "should be hhmmss")
#        print(seconds, "again, but should now be a string of ss.00")# yes
        seconds = int(seconds)
#        print(seconds, "again, but should now be an integer of ss.00")# yes
        # This next line does not replace!
        #data.loc[i, 'timeStart'] = seconds#does not replace. adds and stacks
        #data.loc['timeStart'] = seconds#does not replace
        tempCol.append(seconds)
#        print(hrule)

    return tempCol

#############################################
### Convert any time formats to integers
#print(hrule, "From line 148: Data Types of Each Column:\n", data.dtypes)

### Sometimes the time is viewed as an object. Convert.





def findColumn(df):

    ### Empty String to send later
    fixCol = ""
    columnCount = 0

    ### Check for the word 'time' in the column names. It is ideal to check for
        # datetime format but often, and especially from what I've seen online
        # for the troubleshooting, you cannot rely on that. 
        #TODO: update this code to check for datatime, object.
    for i in df.columns:
        columnCount += 1
#        print("from line 166 and not in inner loop:", i)
        if "time" in i:
            fixCol = i
#            print(Hrule, "Name of current fixCol=", fixCol)

            ### Send the column to be fixed to the function:
#            print(Hrule, "Now sending fixCol to function:")
            tempCol = []
            tempCol = convert_datetime_integer(df[fixCol])

            ### This should print out a column of integers, in total seconds:
#            print(hrule, "from line 177: tempCol outside of function:")

#            for i in tempCol:
#                print("from line 180:", i)

            ### Insert this converted data as a new column of data frame:
            data.insert(columnCount, fixCol+"_Int", tempCol, True)

            temp_df = pandas.DataFrame(df)
            temp_df.to_csv("../data/"+fixCol+"_temp_df_from_doNotCommit_Cleaned.csv")

        ### Print statement to check before I created it into a function.
        ### Don't delete this yet
        #for j in data["timeStart"]:
        #    print(j)
        #print(Hrule, data["timeStart"])

        ### Save temporarily-altered dataframe to a csv file in working directory

findColumn(data)





# USE THIS as an easy way to quit the program for now
sys.exit()
###################################################################
'''

# Getting to know your data:
print("\nRaw Data info():", rawData.info())


# Describe data with basic statistics (numerical data only):
print("\n\n Describe Data:\n", rawData.describe(), "\n\n")

# Describe using a parameter and numpy:
print("\n\n Describe Data with parameter:\n:", rawData.describe(include=object))

###############################################################################

# Ask questions about these numbers:
print("\n\n", "-"*60, "\n\nIf the top question verb is 'clarify' and the top question noun is"
        " 'stabilizedVictim', then why is the top question label"
        " 'clarifyCriticalLocation'?")

print("\nQuestion Verb Count:\n", rawData["questionVerb"].value_counts())

##############################################################################
# Print all unique label values in a column:

print("\n", "-"*60, "\nQuestion Verbs\n")
print(rawData["questionVerb"].unique())

print("\n", "-"*60, "\nCause Verbs\n")
print(rawData["causeVerb"].unique())

print("\n", "-"*60, "\nEffect Verbs\n")
print(rawData["effectVerb"].unique())



##############################################################################
#This function grabs all nouns, verbs and modifiers from labels from cvs.
#It does not separate from the label itself, yet.

# combines from cause, question and effect to make a set of unique values
def labelList(a, b, c, title):
    a = a.tolist()
    b = b.tolist()
    c = c.tolist()
    dlist = []
    d = a + b + c
    d = [x for x in d if str(x) ==x]

    for j in range(len(d)):
        d[j] = d[j].lower()

    d = list(set(list(d)))
    d = sorted(d)

    print("\n\n\n", "-"*30, title, ":  All after appending\n")
    for i in d:
        print(i)

    return d


allVerbs = labelList((rawData["questionVerb"].unique()),
        (rawData["effectVerb"].unique()),
        (rawData["causeVerb"].unique()),
        "VERBS")
allNouns = labelList((rawData["questionNoun"].unique()),
        (rawData["effectNoun"].unique()),
        (rawData["causeNoun"].unique()),
        "NOUNS")
allMods = labelList((rawData["questionModifier"].unique()),
        (rawData["effectModifier"].unique()),
        (rawData["causeModifier"].unique()),
        "MODIFIERS")

#####  #####  #####  #####  ##### 
##############################################################################
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


 #####  #####  #####  #####  #####

resolve_redundant_list = []
resolve_redundant_list = resolveRedundancies(allVerbs, allNouns, allMods, "Verb", "Noun", "Modifier")
print("\n", "="*60, "\n")


##############################################################################

#print("\nQuestion Noun Count:\n", rawData["questionNoun"].value_counts())

# Use .loc or iloc

print("\n\n", "-"*60, "\nNoun: stabilizedVictim \t Verb: any \nWhat other verbs are found with 'stabilizedVictim'?\n")
print(rawData.loc[rawData["questionNoun"] == "stabilizedVictim", "questionVerb"].value_counts())



print("\n\n", "-"*60, "\nNoun: any \t Verb: clarify \nWhat other nouns are found with 'clarify'?\n")
print(rawData.loc[rawData["questionVerb"] == "clarify", "questionNoun"].value_counts())



print("\n\n", "-"*60, "\nThen why does 'critical' and 'clarify' seem to go together"
        " when the frequency counts of each does not support this idea?\n")
print("\nNoun: any \t Verb: clarify\n", rawData.loc[rawData["questionVerb"] == "clarify", "questionNoun"].value_counts())



print("\n\n", "-"*60, "\nNoun: critical \t Verb: any \n", rawData.loc[rawData["questionNoun"] == "critical", "questionVerb"].value_counts())

print("\n\t", "\nNoun: location \t Verb: any \n", rawData.loc[rawData["questionNoun"] == "location", "questionVerb"].value_counts())

print("\n\t", "\n Modifier: location \t Verb: any \n", rawData.loc[rawData["questionModifier"] == "location", "questionVerb"].value_counts())



print("\n\n", "="*60, "\nOn average, how many seconds remain when people ask 'clarifyCriticalLocations?\n")
print(round(rawData.loc[rawData["questionLabel"] == "clarifyCriticalLocation",
    "start"].mean(), 1), "Seconds Remaining.")



print("\n", "="*60, "\n")
###################################################################

# Query Data for Specific Observations. In this case, all question verbs that
# have 'clarify', question nouns that have 'location' or 'critical' or
# 'stabilizedVictim'.

clarify = rawData[rawData["questionVerb"] == "clarify"]
pandas.set_option('display.max_rows', 10)
pandas.set_option('display.max_columns', 25)
pandas.set_option('display.width', 200)
pandas.set_option('display.colheader_justify', 'center')
pandas.set_option('display.precision', 1) # decimal place

print("\n\n", "="*60)
print("Top 6 observations with question verb == 'clarify'")
print("Shape of Clarify:", clarify.shape)
print("\nQuestion Verb Count:\n", clarify["questionVerb"].value_counts())
print("\nQuestion Noun Count:\n", clarify["questionNoun"].value_counts().head(6))
print("\nQuestion Modifier Count:\n", clarify["questionModifier"].value_counts().head(6))


print("\n\n", "="*60)
location = rawData[rawData["questionNoun"] == "location"]

pandas.set_option('display.max_rows', 10)
pandas.set_option('display.max_columns', 25)
pandas.set_option('display.width', 200)
pandas.set_option('display.colheader_justify', 'center')
pandas.set_option('display.precision', 1) # decimal place

print("All observations with question location == 'location'")
print("Shape of Location:", location.shape)
print("\nQuestion Verb Count:\n", location["questionVerb"].value_counts())
print("\nQuestion Noun Count:\n", location["questionNoun"].value_counts())
print("\nQuestion Modifier Count:\n", location["questionModifier"].value_counts())


print("\n\n", "="*60)
stabilizedVictim= rawData[rawData["questionNoun"] == "stabilizedVictim"]

pandas.set_option('display.max_rows', 10)
pandas.set_option('display.max_columns', 25)
pandas.set_option('display.width', 200)
pandas.set_option('display.colheader_justify', 'center')
pandas.set_option('display.precision', 1) # decimal place

print("All observations with question Noun== 'stabilizedVictim'")
print("Shape of stabilizedVictim Datafram:", stabilizedVictim.shape)
print("\nQuestion Verb Count:\n", stabilizedVictim["questionVerb"].value_counts())
print("\nQuestion Noun Count:\n", stabilizedVictim["questionNoun"].value_counts())
print("\nQuestion Modifier Count:\n", stabilizedVictim["questionModifier"].value_counts())



print("\n", "="*60, "\n")
###################################################################

# Get rid of null values
print("Shape of data before cleaning out cause verb nulls:", rawData.shape)
cleaned = rawData[rawData["causeVerb"].notnull()]
print("Shape of data AFTER cleaning out nulls:", cleaned.shape)
print("\n", "="*60, "\n\n\n")



# Find all observations of the person clarifying something that had the effect
# of ask or further clarification:
moreClarifying = rawData[(rawData["questionVerb"] == "clarify") &
        (rawData["effectVerb"] == "ask") |
        (rawData["effectVerb"].str.startswith("clar"))]

print("\n This moreClarifying Chain Shape:", moreClarifying.shape)

print("\n", "="*60, "\n")
###################################################################





print("\n Find all nouns used for verbs clarify, verify, specify, check or answer.")
print("\n", (rawData["questionLabel"].str.startswith("clar")))

print("\n", "="*60, "\n")
###################################################################

# Group By
### Never sort your subsets when creating with groupby. Use the parameter of
    # sort = FALSE when creating!


#print("\n\nHow many question verbs of clarifying resulted with effect verbs"
#        " of 'ask' or 'clarify'? ")

#print("Shape of clarify before:", clarify.shape)

# Create a dataframe that uses ask or clarify in effectVerb with groupby()
# function:
#print("\n", "="*60, "\n")
#print("\nMoreClarifying grouped by 'effectVerb'",
#        moreClarifying.groupby("effectVerb", sort=False), value_counts())




###################################################################
# Find all uses of verb intended for specific noun.
query = 'collaborate'

print("\n\n", "-"*60, "\nVerb:", query, "\n:")
print("In cause:")
print(rawData.loc[rawData["causeVerb"] == query, "causalLabel"].value_counts())
print("\nIn question:")
print(rawData.loc[rawData["questionVerb"] == query, "questionLabel"].value_counts())
print("\nIn effect:")
print(rawData.loc[rawData["effectVerb"] == query, "effectLabel"].value_counts())
print("\n", "="*60, "\n")
###################################################################




#Clean out columns while working with data
print("Raw Data Shape before Dropping and Cleaning:", rawData.shape)

cleaned = rawData.copy()
print("Type for 'clean dataframe should be data frame:" , type(cleaned))

# Print column names:
for col in cleaned.columns:
    print(col)


print("\n", "="*60, "\n")
###################################################################


# Convert to data frame then clean out some columns:
cleaned = pandas.DataFrame(cleaned)


# Method 1: Cleaner but uses extra variable. Use if repeatable. 
toDrop = ["duration", "player", "timeStart", "timeEnd", "question", "context"]
cleaned = cleaned.drop(toDrop,  axis=1)

# Method 2: More explicit and readable
#cleaned = cleaned.drop("timeStart",  axis=1)
#cleaned = cleaned.drop(["timeEnd", "question", "context"],  axis=1)

# Print column names:
for col in cleaned.columns:
    print(col)

print("Cleaned Raw Data:", cleaned.shape)



print("\n", "="*60, "\n")
###################################################################


# Find unique values, counts, and other manipulations
unique_qVerbs = cleaned["questionVerb"].nunique()
print("\n\n Unique Question Verbs:", unique_qVerbs)
print("Type for unique qVerbs:", type(unique_qVerbs))

print("\n\n", "-"*60, "\n")


###################################################################

# These are categorical variables.
count_qVerbs = cleaned["questionVerb"].value_counts()
print("Value counts:\n", count_qVerbs)

print("\n\n", "-"*60, "\n")
print("Type for count_qVerbs:", type(count_qVerbs))

print("\n\n", "-"*60, "\n")
# Turn datatype into categorical for saving memory
    # First see what we have after we cleaned before datatype conversion:

    # Make sure it's a dataframe:
count_qVerbs = pandas.DataFrame(count_qVerbs)
    # Check with info() to see what we have for data type:
print("\n qVerbs Info():", count_qVerbs.info())

# Now change some categorical data:
count_qVerbs = pandas.Categorical(count_qVerbs)
print("\n qVerbs dtype():", count_qVerbs.dtype)



print("\n", "="*60, "\n")
###################################################################
###################################################################
###################################################################
###################################################################


import matplotlib.pyplot as pyplot

# Series and Dataframes have a .plot() wrapper. Line plot by default.

# Plot a bar chart
rawData["questionVerb"].value_counts().head(30).plot(kind="bar")
pyplot.show()

rawData = rawData[rawData["questionVerb"].notnull()]

pyplot.scatter(rawData["questionVerb"], rawData["questionNoun"])
pyplot.xlabel("Question Verbs")
pyplot.xticks(rotation=-90)
pyplot.ylabel("Question Nouns")
pyplot.title("Question Verbs and Nouns")

pyplot.show()




pandas.set_option('display.max_rows', 15)


#        rawData.loc[rawData["questionVerb"] == "confirm",
#        rawData.loc[rawData["questionVerb"] == "verify",
#        rawData.loc[rawData["questionVerb"] == "check",
#        rawData.loc[rawData["questionVerb"] == "specify",
#        rawData.loc[rawData["questionVerb"] == "acknowledge",
#        rawData.loc[rawData["questionVerb"] == "answer",


###This function accepts desired verb, data frame and number for head().
# Returns Nouns of verb constraints.
def verbNounMod(constraint, df, head_num):
    print("\n\n", "-"*60, "\nQuestion Verb:", constraint, "\n Question Nouns\n", "-"*60, "\n",
            df.loc[df["questionVerb"] == constraint,
                "questionNoun"].value_counts().head(head_num))

    print("\n\n", "-"*60, "\nEffect Verb:", constraint, "\nEffect Nouns\n", "-"*60, "\n",
            df.loc[df["effectVerb"] == constraint,
                "effectNoun"].value_counts().head(head_num))

    print("\n\n", "-"*60, "\nCause Verb:", constraint, "\nCause Nouns\n", "-"*60, "\n",
            df.loc[df["causeVerb"] == constraint,
                "causeNoun"].value_counts().head(head_num))
    print("\n", "="*60, "\n")


#verbNounMod("clarify", rawData, 10)
##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### #####
'''










