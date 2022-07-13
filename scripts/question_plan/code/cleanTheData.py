"""
--------------------------------------------------------------------------
Purpose:
    This program reads in a csv file from annotations written in camel-case
    verbObjectObject form, time, raw text annotation, and other features
    annotated from the ASIST Minecraft SAR Environment Study 3 data.

    This program does not import HSR Data.

    Set RUN_TESTABC = TRUE (line 58) to print cleaned labels.

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Created:
    18 June 2022

Last Updated:
    12 July 2022

Affiliation:
    Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
    Adarsh Pyarelal, Head PI and Clayton T. Morrison, Co-PI
    School of Information, University of Arizona
--------------------------------------------------------------------------

Functions in File:
    1. getRawData(filename)
    2. cleanLabels(df, dirtyCol)
    3. convert_datetime_integer(column)
    4. find_time_column(df)
    5. alphabetizeObjects(column)
    6. main(csv file)

Attributes of comments in file to be aware of:
    '###' Single-line comments for user.
    '#' Commands that can be uncommented. Most of these are either print
        statements for debugging or data exploration samples/ heads.
--------------------------------------------------------------------------
"""

#--------------------------------------------------------------------------
### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*80 + "\n")
Hrule = ("\n" + "="*80 + "\n")

import sys
import numpy
import pandas
import requests
import time
import datetime


### Set to true or false to print labels for verification of being cleaned
RUN_TESTABC = True
#--------------------------------------------------------------------------

def convert_datetime_integer(column):
    """
    Purpose:
        Convert datetime to integer timestamp. Since players refer to time in
        terms of "time left," the data are formatted in descending order.

        The dt() function often mentioned in tutorials is depreciated, so I created an
        alternate solution (Salena Ashton, 20 June 2022).

    Args:
        column: Called from find_time_column() and sends the selected column
            to be converted from datetime format.

    Returns:
        Returns a column of total seconds as integers to the find_time_column() function.
    """

    ### Convert column into its own dataframe
    column = pandas.to_datetime(column)

    ### Remove dates and then convert to seconds
    column = pandas.Series([val.time() for val in column])
    tempCol = []

    for i in column:
        time = str(i)
        time = time[:-3]
        date_time = datetime.datetime.strptime(time, "%M:%S")
        a_timedelta = date_time - datetime.datetime(1900, 1, 1)
        seconds = a_timedelta.total_seconds()
        seconds = int(seconds)
        tempCol.append(seconds)

    return tempCol ### returns fixed column to find_time_column()


def find_time_column(df):
    """
    Purpose:
        Finds column names with the word 'time' and verifies that it can be
        converted from any datatype to an integer to count seconds.

    Args:
        df: dataframe with datetime formats

    Returns:
        df: dataframe with cleaned time column (integer)

    """
    ### Empty String to send later
    fixCol = ""
    columnCount = 0

    ### Check for the word 'time' in the column names. It is ideal to check for
        ### datetime format but often, and especially from what I've seen online
        ### for the troubleshooting, you cannot rely on that. 
        ###TODO: update this code to check for datatime, object.
    for i in df.columns:
        columnCount += 1
        if "time" in i:
            fixCol = i

            ### Send the column to be fixed to the function:
            tempCol = []
            tempCol = convert_datetime_integer(df[fixCol])

            ### Insert this converted data as a new column of data frame:
            newFixCol = fixCol[4:] # Remove 'time' from column name
            df.insert(columnCount, newFixCol+"Seconds", tempCol, True)

            ### Remove original datetime formatted column
            df.drop(fixCol, inplace = True, axis = 1)

            ### Save temporarily-altered dataframe to a csv file in working directory
            temp_df = pandas.DataFrame(df)
            temp_df.to_csv("../data/temp_csv_folder/"+fixCol+"_temp_df_from_doNotCommit_Cleaned.csv")

    return df


### Replace labels as created by annotators with alphabetized labels
def alphabetizeObjects(column):
    """
    Purpose:
        Annotation Labels come in the form "verbObjectObject". This function
        alphabetizes both objects after the verb to avoid duplication of labels
        that are the same in meaning.

        Example:
            Raw Labels: "clarifyVictimLocation", "collaborateCarryStabilized",
            and "clarifyLocationVictim." Because annotators were given full
            autonomy in label creation during annotation, many labels are not
            in a specific order of objects. This raw list has three labels but
            only two meanings.

            Cleaned labels: "clarifyLocationVictim" and
            "collaborateCarryStabilized."

        Labels have a verb, an object, and optional second object. This
        function will only work for labels written in Camel Case.

    Args:
        column: A column of labels to be cleaned. Columns are currently
        hard-coded within the main() function.

    Returns:
        newColumn: Original column of labels in cleaned form.
        allVerbs: a list of all verbs used in annotation.
        allNM: a list of all objects that were used as modifiers or nouns.
    """

    def getLabels(myLabel):
        """
        Purpose:
            This function is called from alphabetizeObjects and splits the label
            into verbs and objects, then alphabetizes the objects before
            reassembling the label.

        Args:
            myLabel: Each label found in the column sent to this function.

        Returns:
            myVerb: The verb from a specific label in the column iteration.
            myNoun: The specific noun or first object.
            myModifier: The specific modifier or second, optional object.
            myABC: The full label, alphabetized with verb first.

        """
#        print(hrule, "from getLabels():", myLabel)

        def getVerb(label):
            """
            Args:
                label: Unclean label from column to be cleaned.

            Returns:
                verb: The verb from the label.
                label: Remainder of label object(s).

            """
#            print("from getVerb()", label)
            verb = ""
            size = len(label)
            size = int(size)
            for j in label:
                if size < 1:
                    label = "Nomodifier"
                    return verb, label
                elif j.islower():
                    verb = verb + j
                    label = label.replace(j, "", 1)
                    size -= 1
                    if size < 1:
                        label = "Nomodifier"
                        return verb, label
                else:
                    return verb, label

        def getNoun(label):
            """
            Args:
                label: Label objects after verb is removed.

            Returns:
                noun: First object removed from label.
                label: Remainder of label (second object, if present).

            """
#            print("from getNoun()", label)

            ### Remove capital letter for noun:
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
            """
            Args:
                Label: Remainder of label after verb and first object are removed.

            Returns:
                modifier: Last object removed from label or blank if no second object
                    were present.
            """

            size = len(label)
            if size < 1:
                modifier = ""
                return modifier

            modifier = label[0].lower()
            label = label.replace(label[0], "", 1)
            modifier = modifier + label
            ### Since we don't have a break for uppers, use length:
            return modifier

        def abcOrder(myV, myN, myM):
            """
            Purpose:
                Reassemble label components back into verbObjObj in
                alphabetical order.

            Args:
                myV: The verb from the label in current iteration of column.
                myN: The noun from the label in current iteration of column.
                myM: The modifier, if present, from the label in current
                    iteration of the column.

            Returns:
                ABCLabel: alphabetized label
            """
            abcLabel = ""
            if myM=="":
                first = myN[0].upper()
                myN = first+myN[1:]
                abcLabel = myV+myN

            elif myN[0] > myM[0]:
#                print("Oh no!",  myN[0], "<?>", myM[0])
                temp = myN
                myN = myM
                myM = temp
                first = myN[0].upper()
                myN = first+myN[1:]
                second = myM[0].upper()
                myM = second+myM[1:]
                abcLabel = (myV+myN+myM)

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

    allNouns = []
    allVerbs = []
    allNM = []
    allModifiers = []
    newColumn = []

    for i in column:
        token = str(i)
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


#    print(hrule, "All Verbs:\n", allVerbs)
#    print(hrule, "All Nouns:\n", allNouns)
#    print(hrule, "All Modifiers:\n", allModifiers)
#    print(hrule, "NewColumn of myABC Labels:\n")
#    for c in newColumn:
#        print(c)
    return newColumn, allVerbs, allNM



def getRawData(filename):
    """
    Purpose:
        To clean labels from camel-case format in human annotation.
        Reads file into a pandas dataframe format, removes null values, selects
        features to be cleaned, display preferences, and converts select
        columns into integer types.

    Args:
        filename: User-specified file name of csv to be cleaned.

    Returns:
        data: Dataframe format of csv file.
    """

    ### If not in csv format, use read_json(), read_html(), read_sql_table()
    rawData = pandas.read_csv(filename)

    ### Examine the Data
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


    ### Deep copy of dataframe to focus on conditional probabilities of labels
        # If no deep copy is made, several warnings will result. 
        # Reference used to solve copy problem: https://www.dataquest.io/blog/settingwithcopywarning/
    data = rawData[["video", "obsNum", "regular", "critical", "score", "timeStart", "timeEnd",
    "htn", "abstractLabel", "causeLabel", "questionLabel",
    "effectLabel", "qWord", "qPhrase", "auxVerb", "actionVerb"]].copy(deep =
            True)
#    print("Shape of selected-feature data:", data.shape, hrule)

    ### Helpful examination of numerical data
#    print(hrule, "\nData info():\n", data.info())
#    print(hrule, "\nDescribe Data:\n", data.describe(), "\n")

    ### Describe using a parameter and numpy. Helpful for categorical data.
#    print(hrule, "\nDescribe Data with Parameter:\n", data.describe(include=object))

    ### No need for floats in this data. Convert all floats to integers:
    data["video"] = rawData["video"].astype(int)
    data["obsNum"] = data["obsNum"].astype(int)
    data["regular"] = data["regular"].astype(int)
    data["critical"] = data["critical"].astype(int)
    data["score"] = data["score"].astype(int)

    return data


def cleanLabels(df, dirtyCol):
    """
    Purpose:
        Converts datetime datatypes, cleans annotator labels
        and cleans dataframes. Use for scalability in this format.

    Args:
        df: Dataframe of columns to be cleaned.
        dirtyCol: Column needing to be cleaned.

    Returns:
        cleaned: Dataframe ready for data snooping after cleaning
    """

    ### Reinspect and Describe using a parameter and numpy:
    cleaned = df.copy(deep=True)
    #print(hrule, "Shape of cleaned data:", cleaned.shape)
    cleaned = find_time_column(cleaned)
    #print(hrule, "With new columns for time, Shape of cleaned data:", cleaned.shape)

    ### Create a new column to alphabatize verbObjectObject:
    abcColumn = []
    abcColumn, allV, allNM = alphabetizeObjects(cleaned[dirtyCol])


    ### Get column Index of labels to be cleaned so I can place the new column
        ### next to it:
    labelIndex = cleaned.columns.get_loc(dirtyCol)
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
    return cleaned


def main(filename):
    """
    Purpose:
        Clean data, whether called from this file or another file.

    Args:
        filename: relative path to non-HSR data

    Returns:
        myData: cleaned dataframe to be used for additional text cleaning
    """

    print(hrule, "Cleaning columns...\n\n")
    myData = getRawData(filename)
    myData = cleanLabels(myData, "abstractLabel")
    myData = cleanLabels(myData, "htn")
    myData = cleanLabels(myData, "causeLabel")
    myData = cleanLabels(myData, "effectLabel")
    myData = cleanLabels(myData, "questionLabel")
    HSR = pandas.DataFrame(myData)
    HSR.to_csv("../data/data_noHSR_readyForUse.csv")
    return myData

def testABC(df, col):
    """
    Purpose:
        Prints list of all labels after cleaning in order to verify the labels
        were cleaned correctly. User must specify "True" or "False" on line 58
        to execute this function.
    """
    df = df[col].sort_values().unique()
    for d in df:
        print(d)


###############################################################################
#   Program Starts Here
###############################################################################

if __name__ == '__main__':
    ### Read in the Data:
    file = "../data/commitOKAY_HSR-Removed_raw.csv"

    ### Start Cleaning Process from main()
    myCleanedData = main(file)

    ### Test abc order of labels
    if RUN_TESTABC:
        testABC(myCleanedData, 'questionLabels')

###############################################################################
#   End of Program
###############################################################################
