'''
--------------------------------------------------------------------------
This code will not run until I upload the csv data.

Program begins around line 410.
--------------------------------------------------------------------------

Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 18 June 2022
Last Updated: 19 June 2022

Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
Planning Work Group
Adarsh Pyarelal, Head PI and Clayton T. Morrison, Co-PI
School of Information, University of Arizona
--------------------------------------------------------------------------

Purpose: cleanTheData.py takes in annotations written in camel-case
    verbObjectObject form, time, and other features annotated from study 3
    data from ASIST's Minecraft SAR Environment.

Functions in File:
    1. getRawData(filename)
        * Reads in csv file. See note on line 2.
        * Returns dataframe with features of interest
    2. cleanLabels(df, dirtyCol)
        * Calls out to 3 Functions:
    3.     * convert_datetime_integer(column)
             * converts timestamps to total seconds
    4.     * find_time_column(df)
             * locates other columns that need conversions
    5.     * alphabetizeObjects(column)
             * splits parts of speech, checks for missing modifiers,
               checks for missing nouns, reorders labels for convention,
               and returns cleaned columns for all labels sent in the
               verbObjectObject format.

This file creates temporary files (when uncommented).
--------------------------------------------------------------------------
'''


###################################################################
### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*76 + "\n")
Hrule = ("\n" + "="*76 + "\n")
###################################################################

import sys
import numpy
import pandas
import requests
import time
import datetime

########################################################################
def convert_datetime_integer(column):
    '''
    Convert datetime to integer timestamp. Since the mission progresses from 900
        start time and ends at 000 seconds, and since players refer to time in
        terms of "time left," I have reflected this in the data format.

    Purpose: Convert object or datatypes into integers.
             Note that the dt() function often mentioned in tutorials is
             depreciated and most solutions found online do not work.
    Input:   Called from find_time_column() and sends the
             Selected column that has word 'time' in name.
    Output:  Returns a column of total seconds as integers to the
             find_time_column() function.
    '''

    column = pandas.to_datetime(column)
#    print(hrule, "Data Types of Each Column:", data.dtypes)
    ### Remove dates and then convert to seconds
    column = pandas.Series([val.time() for val in column])
    tempCol = []

    for i in column:
#        print(i, "is START data type:", type(i))
        time = str(i)
        time = time[:-3]
        date_time = datetime.datetime.strptime(time, "%M:%S")
        a_timedelta = date_time - datetime.datetime(1900, 1, 1)
        seconds = a_timedelta.total_seconds()
        seconds = int(seconds)
        tempCol.append(seconds)
#        print(hrule)

    return tempCol # returns fixed column to find_time_column()



########################################################################

def find_time_column(df):
    '''
    Purpose: Finds column names with the word 'time' and verifies that it
             can be converted from any datatype to an integer to count seconds.
    Input:   Takes in a dataframe and reads the name of each column head.
    Process: Sends to convert_datatime_integer() function to convert. 
    Output:  Returns a column of total seconds as integers to the
             find_time_column() function.
    '''
    ### Empty String to send later
    fixCol = ""
    columnCount = 0

    ### Check for the word 'time' in the column names. It is ideal to check for
        # datetime format but often, and especially from what I've seen online
        # for the troubleshooting, you cannot rely on that. 
        #TODO: update this code to check for datatime, object.
    for i in df.columns:
        columnCount += 1
        if "time" in i:
            fixCol = i
#            print(hrule, "Name of current fixCol=", fixCol)

            ### Send the column to be fixed to the function:
            tempCol = []
            tempCol = convert_datetime_integer(df[fixCol])

            ### Insert this converted data as a new column of data frame:
            newFixCol = fixCol[4:] # Remove 'time' from column name
            df.insert(columnCount, newFixCol+"Seconds", tempCol, True)

            ### Remove original datetime formatted column
            df.drop(fixCol, inplace = True, axis = 1)

            ### Check Dataframe within this function and loop
            #print(hrule, "Checking dataframe with updated", fixCol, "Column:\n", df.head())

            ### Save temporarily-altered dataframe to a csv file in working directory
            temp_df = pandas.DataFrame(df)
            temp_df.to_csv("../data/temp_csv_folder/"+fixCol+"_temp_df_from_doNotCommit_Cleaned.csv")

    return df

#####################################################################################

### Replace labels as created by annotators with alphabetized labels
def alphabetizeObjects(column):
    '''
    Purpose: Independent annotators were given least-restrictive labeling
             as long as they adhered to the procedures of Grounded Theory.
             Because of this, some labels, like 'askLocationVictim' and
             'askVictimLocation' register as two separate labels. This main
             function corrects all labels to keep original verb, then it
             alphabetizes the two objects. Not all labels have 2 objects.
    Input:   dataframe column of labels to be cleaned
    Process: getLabels() splits into parts of speech and alphabetizes objects.
    Output:  returns parts of speech and cleaned labels for column.
             removes old column and inserts new column automatically.
    '''
    def getLabels(myLabel):
#        print(hrule, "from getLabels():", myLabel)

        def getVerb(label):
#            print("from getVerb()", label)
            verb = ""
            for j in label:
                if j.islower():
                    verb = verb + j
                    label = label.replace(j, "", 1)
                else:
#                    print("\nFrom getVerb():\n", verb)
                    return verb, label

        def getNoun(label):
#            print("from getNoun()", label)
            # remove capital letter for noun:
            noun = label[0].lower()
            label = label.replace(label[0], "", 1)
            size = len(label)
            size = int(size)
            for k in label:
                if size<1:
                    label = "nomodifier"
                    return noun, label
                elif k.islower():
                    noun = noun + k
                    label = label.replace(k, "", 1)
                    size -= 1
                    if size<1:
                        return noun, label
                else:
                    return noun, label

        def getModifier(label):
            size = len(label)
            if size < 1:
#                print("size:", size)
#                print("NO MODIFIER")
                modifier = ""
                return modifier

            modifier = label[0].lower()
            label = label.replace(label[0], "", 1)
            modifier = modifier + label
            # Since we don't have a break for uppers, use length:
            return modifier

        def abcOrder(myV, myN, myM):
            abcLabel = ""
#            print(hrule, myV, myN, myM)
            if myM=="":
                first = myN[0].upper()
#                print(first)
                myN = first+myN[1:]
#                print("capitalized myN:", myN)
                abcLabel = myV+myN
#                print("abcLabel = ", abcLabel)
#                return abcLabel

            elif myN[0] > myM[0]:
#                print("\nLabel to alphabetize:", myV, myN, myM)
#                print("Oh no!",  myN[0], "<?>", myM[0])
                temp = myN
                myN = myM
                myM = temp
#                print("Is it fixed?",  myN[0], "<?>", myM[0])
                first = myN[0].upper()
#                print(first)
                myN = first+myN[1:]
#                print("capitalized myN:", myN)
                second = myM[0].upper()
#                print(second)
                myM = second+myM[1:]
#                print("capitalized myM:", myM)
                abcLabel = (myV+myN+myM)
#                print("\tabcLabel = ", abcLabel)

            else:
                first = myN[0].upper()
                myN = first+myN[1:]
                second = myM[0].upper()
                myM = second+myM[1:]
                abcLabel =(myV+myN+myM)

            return abcLabel


        myVerb = ""
        nm = ""
        myNoun = ""
        myMod = ""
        myABC = ""

        myVerb, myLabel = getVerb(myLabel)
        myNoun, myLabel = getNoun(myLabel)
        myModifier = getModifier(myLabel)
        myABC = abcOrder(myVerb, myNoun, myModifier)

#        print("\nVerb:", myVerb, "\nNoun:", myNoun, "\nModifier:", myModifier)

        return myVerb, myNoun, myModifier, myABC
            ### make verb, noun, and modifier lists from dataframe:

    allNouns = []
    allVerbs = []
    allNM = []
    allModifiers = []
    newColumn = []

    for i in column:
#        print("from alpha()", i)
        token = str(i)
 #       print("Token:", token)
        v, n, m, c = getLabels(token)
        if len(m) > 0:
            M = m[0].upper()
            m = M+m[1:]
        nm = (n+m)
        allNM.append(nm)
        allVerbs.append(v)
        allNouns.append(n)
        allModifiers.append(m)
        newColumn.append(c)


    # probability of the feature of interest.
    def jointProb(allList):
        df = pandas.DataFrame(allList)
        pandas.set_option('display.float_format', '{:.2}'.format)
        df.columns = ["POS"]
        print(df)
        dfa = df['POS'].value_counts(normalize = True).sort_values().to_frame()
        dfa.reset_index(inplace = True)
        dfa.columns = ['0', 'joint_probability']
        print(dfa.head(100), hrule)

#    jointProb(allModifiers)




#    print(hrule, "All Verbs:\n", allVerbs)
#    print(hrule, "All Nouns:\n", allNouns)
#    print(hrule, "All Modifiers:\n", allModifiers)
#    print(hrule, "NewColumn of myABC Labels:\n")
#    for c in newColumn:
#        print(c)
    return newColumn, allVerbs, allNM



##################################################################################### |

def getRawData(filename):
    '''
    Purpose:
    Input:
    Process:
    Output:
    '''

    rawData = pandas.read_csv(filename)
    ### If not in csv format, use read_json(), read_html(), read_sql_table()

    ### EXAMINE THE DATA
    print("Shape of raw data:", rawData.shape)

    ### Get rid of null values
    rawData = rawData[rawData["obsNum"].notnull()]
    print("Shape of data AFTER cleaning out nulls:", rawData.shape)

    ### Set up display for convenience in reading output:
    pandas.set_option('display.max_rows', 40)
    pandas.set_option('display.max_columns', 22)
    pandas.set_option('display.width', 150)
    pandas.set_option('display.colheader_justify', 'center')
    pandas.set_option('display.precision', 1) # decimal place


    ### Subset dataframe to focus on conditional probabilities of labels
    data = rawData[["video", "obsNum", "regular", "critical", "score", "timeStart", "timeEnd",
    "question_verbatim", "htn", "abstractLabel", "causeLabel", "questionLabel",
    "effectLabel", "qWord", "qPhrase", "auxVerb", "actionVerb"]]
#
#    print("Shape of selected-feature data:", data.shape, hrule)
    ###################################################################
    ### Getting to know the Data:
    #print(hrule, "\nData info():\n", data.info())

    ### Not as helpful for my research question 
 #   print(hrule, "\nDescribe Data:\n", data.describe(), "\n")

    ### Describe using a parameter and numpy:
 #   print(hrule, "\nDescribe Data with Parameter:\n", data.describe(include=object))

    ### Print data types of columns:
    ### No need for floats in this data. Convert all floats to integers:
    #print(hrule, "\nData Types of Each Column:\n", data.dtypes)
    data["video"] = data["video"].astype(int)
    data["obsNum"] = data["obsNum"].astype(int)
    data["regular"] = data["regular"].astype(int)
    data["critical"] = data["critical"].astype(int)
    data["score"] = data["score"].astype(int)
    #print(hrule, "Data Types of Each Column:\n", data.dtypes)

    return data
#####################################################################################


def cleanLabels(df, dirtyCol):
    '''
    Purpose: converts datetime datatypes, cleans annotator labels
             and cleans dataframes. Use for scalability.
    Input:   df = dataframe of columns to be cleaned
             dirtyCol = column needing to be cleaned
    Output:  dataframe ready for data snooping after cleaning
    '''
    ########################################################
    ### Uncomment to Verify the column passes in correctly:

    #print(hrule, "verify column passes in correctly:", hrule)
    #for d in dirtyCol:
    #    print(d)

    #print(hrule, "dirtyCol End from cleanLabels()", hrule)
    ########################################################


    ### Reinspect and Describe using a parameter and numpy:
    cleaned = df.copy(deep=True)
    #print(hrule, "Shape of cleaned data:", cleaned.shape)
    cleaned = find_time_column(cleaned)
    #print(hrule, "With new columns for time, Shape of cleaned data:", cleaned.shape)


    ########################################################
    ### Create a new column to alphabatize verbObjectObject:
    abcColumn = []
    abcColumn, allV, allNM = alphabetizeObjects(cleaned[dirtyCol])

    ### Uncomment to Verify the column passes in correctly:

    #print("Check to see if things are passing in this function okay:\n")
    #print("Sending dirtyCol to alphabetizingObjects...")
    #for i in abcColumn:
    #    print(i)

    #print(hrule, "abcColumn End from cleanLabels()", hrule)
    ########################################################

    ### Uncomment to Verify the column passes in correctly:
    #for a in abcColumn:
    #    print("From outer most edge, ready to put back in dataframe:", a)

    ### Get column Index of labels to be cleaned so I can place the new column
        ### next to it:
    labelIndex = cleaned.columns.get_loc(dirtyCol)
    #print(hrule*3, "labelIndex:", labelIndex)
    labelIndex += 1


    ### Remove original dirty column and insert cleaned/ alphabetized column:
    cleaned.insert(labelIndex, dirtyCol+"s", abcColumn, True)
    cleaned.drop(dirtyCol, inplace = True, axis = 1)

    if "questionLabel" in dirtyCol:
        cleaned.insert(labelIndex, dirtyCol+"s_nm", allNM, True)
        cleaned.insert(labelIndex, dirtyCol+"s_v", allV, True)

    if "abstractLabel" in dirtyCol:
        cleaned.insert(labelIndex, dirtyCol+"s_nm", allNM, True)
        cleaned.insert(labelIndex, dirtyCol+"s_v", allV, True)

    if "intention" in dirtyCol:
        cleaned.insert(labelIndex, dirtyCol+"s_nm", allNM, True)
        cleaned.insert(labelIndex, dirtyCol+"s_v", allV, True)

    if "primitiveQuestion" in dirtyCol:
        cleaned.insert(labelIndex, dirtyCol+"s_nm", allNM, True)
        cleaned.insert(labelIndex, dirtyCol+"s_v", allV, True)


#    print(hrule, "Dataframe with Updated", dirtyCol+"s Column:"+"\n\n", cleaned.head())

    ### Save temporarily-altered dataframe to a csv file in working directory
    temp_cleaned = pandas.DataFrame(cleaned)
    temp_cleaned.to_csv("../data/temp_csv_folder/temp_ABC_"+dirtyCol+"_from_doNotCommit_Cleaned.csv")
    return cleaned

#####################################################################################
#           Program Starts Here
#####################################################################################
def main(filename):
    '''
    Purpose: Clean data, whether called from this file or another file.
    '''
    myData = getRawData(filename)
    myData = cleanLabels(myData, "abstractLabel")
    myData = cleanLabels(myData, "htn")
    myData = cleanLabels(myData, "causeLabel")
    myData = cleanLabels(myData, "effectLabel")
    myData = cleanLabels(myData, "questionLabel")
    HSR = pandas.DataFrame(myData)
    HSR.to_csv("../data/doNotCommit2_HSR_readyForUse.csv")
#    print(hrule, "saving to readyForUse file...\n")
    return myData


### Read in the Data:
file = "../data/doNotCommit2_HSR_raw.csv"

### Start Cleaning Process from main()
myCleanedData = main(file)

### Verify
#print(hrule, "\nChecking myCleanedData:\n\n", myCleanedData.head(10), hrule)


#####################################################################################
#   End of Program
#####################################################################################
