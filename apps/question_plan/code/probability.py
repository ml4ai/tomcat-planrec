'''
--------------------------------------------------------------------------
This code will not run from the tomcat-planrec repo until I upload the csv data.
--------------------------------------------------------------------------

Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 20 June 2022
Last Updated: 3 July 2022

Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
Planning Work Group
Adarsh Pyarelal, Head PI and Clayton T. Morrison, Co-PI
School of Information, University of Arizona
--------------------------------------------------------------------------

Purpose: Preliminary Data Snooping of Video Annotations from ASIST's
         SAR Scenario Minecraft Environment, Study 3

Functions in File:
    1. Calls out to cleanTheData.py if annotations need to be cleaned. Note
       that the annotations must follow format conventions in order to be
       cleaned with this file. salena at email dot arizona dot edu for questions.
    2. 

--------------------------------------------------------------------------


Sources used considerably while learning to use Pandas, though none of their
code was used directly for the development of this program:

    https://towardsdatascience.com/8-ways-to-filter-a-pandas-dataframe-by-a-partial-string-or-pattern-49f43279c50f

    https://re-thought.com/pandas-value_counts/

    https://towardsdatascience.com/9-pandas-value-counts-tricks-to-improve-your-data-analysis-7980a2b46536


Sources to consider down the road:
    * Converting wide <-> long data for analysis vs visualization
        * https://www.statology.org/long-vs-wide-data/
'''


import sys
import numpy
import pandas
import requests
import time
import scipy.stats as stats
from sklearn import linear_model
import datetime
import matplotlib.pyplot as pyplot

### Uncomment if you plan to use plotnine
#from plotnine import *


### Will not work from repo until I upload dataset
import cleanTheData as ctd

###############################################################################
def plot_df_fill(df, a, b, c):
    '''
    This function uses R's ggplot() grammar, built on matplotlib

    Input: dataframe, independent variable, dependent variable, categorical var
    Output: any visualization that uses "fill" instead of "color"
    '''
    figure = (ggplot(df,
                    aes(a, b)) +
              geom_tile()
           )
    print(figure)

###############################################################################
    ### Newest and Easiest versions of Probability Functions

def replaceSubstring_Global(df, old, new):
    # Replaces substring in entire dataframe for all columns
    print("\n\t\treplace", old, "with", new)
    df = df.replace(old, new, regex=True)
    return df

def replaceSubstring_Column(df, col, old, new):
    # Replaces in given column
    print("\n\t\treplace", old, "with", new, "\n")
    df[col] = df[col].replace(old, new, regex=True)
    return df

def get_joint_probability(df, colA):
    # Groups by the conditioning element but returns only the JOINT
    # probability of the feature of interest.
    dfa = df[colA].value_counts(normalize = True).sort_values().to_frame()
    dfa.reset_index(inplace = True)
    dfa.columns = [colA, 'joint_probability']
    print(dfa, hrule)
    return dfa

def get_conditional_probability(df, colA, colB):
    print("\nP(", colB, "|", colA, ")\n")
    df1 = df.groupby(colA).value_counts(normalize = True).to_frame()
    df1.reset_index(inplace = True)

    # next line solution from: https://www.codegrepper.com/code-examples/python/pandas+change+the+last+column+name
    df1 = df1.rename(columns={0: 'conditional_probability'})
    print(df1)
    print(hrule)
    return df1


###############################################################################
def replaceTerms(df):
    '''
    Replaces certain terms in the data to reduce granularity of labels.
    Commented-out commands have less impact in reducing number of labels
    that have the joint probability <= 0.0052 (count = 1 for this dataset).
    '''
#    df = replaceSubstring_Global(df, "Room", "Location")
#    df = replaceSubstring_Global(df, "notice", "prioritize")
    df = replaceSubstring_Global(df, "confirm", "clarify")
    df = replaceSubstring_Global(df, "Marker", "Mark")
    df = replaceSubstring_Global(df, "askPlan", "collaborate")
    df = replaceSubstring_Global(df, "CapabilitiesRole",
            "Collaborationcollaborate")
    df = replaceSubstring_Global(df, "Knowledge", "Information")
    df = replaceSubstring_Global(df, "Teammate", "")
    df = replaceSubstring_Global(df, "Stabilized", "Victim")
    df = replaceSubstring_Global(df, "Stabilize", "Victim")
#    df = replaceSubstring_Global(df, "direct", "suggest")
    df = replaceSubstring_Global(df, "askBreak", "request")
    df = replaceSubstring_Global(df, "Collaborationcollaborate",
            "Collaboration")
    df = replaceSubstring_Global(df, "wakeCritical", "collaborateCriticalWake")
    return df

###############################################################################
def plotPrelim(df, x, y, title = "Investigation of Joint Probability Count Granularity"):
    rowCount = df.shape[0]
    colCount = df.shape[1]
    pyplot.scatter(x, y)
    pyplot.xlabel("Joint Probability of Label")
    pyplot.ylabel("Count of Joint Probability Occurrences")
    pyplot.title(title)
    pyplot.show()

###############################################################################

def contingency_tables(df, colA, colB):

    df_table = pandas.crosstab(index=df[colA],
            columns=df[colB], margins = True)

    print(Hrule, "Contingency Table\n\n", df_table, hrule)

    ### This shows some spelling errors. For now, I have corrected them in 
        # the raw csv file, ran cleanTheData.py, and then it comes through here
        # just fine. In the future, if I continue to do this, I'll use a CASDAQ
        # to avoid annotation typos.

###############################################################################

def main(data):
    ### Set some display options
    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 10)
    pandas.set_option('display.colheader_justify', 'center')
    #print(hrule, "Describe Numerical Data:\n", data.describe(), hrule)
    #print(hrule, "Describe Categorial Data:\n", data.describe(include=object), hrule)

    ### Subset the Data
    numData = data[["video", "obsNum", "regular", "critical", "score",
                    "StartSeconds"]]
    catData = data[["htns", "abstractLabels", "question_verbatim",
                    "abstractLabels_v", "abstractLabels_nm", "causeLabels",
                    "questionLabels", "questionLabels_v", "questionLabels_nm",
                    "effectLabels", "qWord", "qPhrase", "auxVerb", "actionVerb"]]

    ### Current subset of interest:
    testdf = catData[['questionLabels', 'qPhrase']]
    jointdfa = get_joint_probability(testdf, 'questionLabels')
    cond1df = get_conditional_probability(testdf, 'questionLabels', 'qPhrase')
    cond2df = get_conditional_probability(testdf, 'qPhrase', 'questionLabels')


    ### Obtain count of joint probabilities, regardless of feature values
    see_joint = jointdfa.groupby('joint_probability').size().to_frame()
    see_joint.reset_index(inplace = True)
    see_joint.columns = ["prob", "count"]
    print(see_joint)
    print(see_joint.shape)


    ### See how the data change label objects are less granular:
    ### Copy subset of data
    rData = replaceTerms(testdf)

    joint_rdf= get_joint_probability(rData, 'questionLabels')
    see_rdf = joint_rdf.groupby('joint_probability').size().to_frame()
    see_rdf.reset_index(inplace = True)
    see_rdf.columns = ['newProb', 'newCount']
    print("\nsee_rdf\n", see_rdf)

    ### Now plot the granular and combined granular:
#    plotPrelim(see_joint, see_joint["prob"], see_joint["count"])

    ### For the question Labels for uncombined, granular labels
    sparse = jointdfa[jointdfa.joint_probability <= 0.01]
    print(hrule, "Sparse Question Labels: Granular\n\n", sparse.head(200))

    ### For the question Labels for combined, less granular labels
    asparse = joint_rdf[joint_rdf.joint_probability <= 0.01]
    print(hrule, "Sparse Question Labels: Combined\n\n", asparse.head(200))

    return data# end of main()
##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### #####

def HSR_main(df):
    '''
    This is the second part of the program that works with HSR Data. The
    following column features are in the df:

        video
        obsNum
        regular
        critical
        score
        StartSeconds
        EndSeconds
        question_verbatim
        htns
        abstractLabels
        abstractLabels_v
        abstractLabels_nm
        causeLabels
        questionLabels
        questionLabels_v
        questionLabels_nm
        effectLabels
        qWord
        qPhrase
        auxVerb
        actionVerb
    '''
    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 12)
    pandas.set_option('display.colheader_justify', 'center')
    pandas.set_option('display.width', 200)



    df = df[['obsNum', 'score', 'StartSeconds', 'question_verbatim',
            'abstractLabels', 'questionLabels', 'qPhrase', 'actionVerb']]
    df = replaceSubstring_Global(df, "Teammate", "")
    df = replaceSubstring_Global(df, "confirm", "clarify")
    df = replaceSubstring_Global(df, "\?", "")
    df = replaceSubstring_Global(df, "Knowledge", "Information")




    '''
    The following Code investigates the difference of intention of a specific
    area verses a general area.

    area, location, rooms (plural) were coded as 'location'
    room was coded as room, if a specific room

    After dividing up the data subsets, I cannot justify this granularity
    between 'room' or 'location' for my research questions, though it may be of
    interest to Liang. 

    Therefore, I will keep this code and the original raw data, cleaned data,
    for others to use. However, I will engage the following replacement  of
    'room' --> 'location'
    for the remainder of this program.
    '''
    df = replaceSubstring_Global(df, "Room", "Location")




    ### Let's work with granular data first:
    print(Hrule, "Now using HSR Data\n\n")
    # Filter for all rows that mention the word 'room'
    room = df['question_verbatim'].str.contains('room', case=False)
    # Now add this 'room' row back into the original dataframe, 
    # The following returns a subset of full dataframe where room
    # was mentioned in the raw text question:
    room = df[room]
    print(hrule, "Rows with \'room\'\n\n", room)

    # Now do the same thing for location and area and rooms (an area):
    rooms = df['question_verbatim'].str.contains('area', case=False)
    rooms = df[rooms]

    area = df['question_verbatim'].str.contains('area', case=False)
    area = df[area]

    loc = df['question_verbatim'].str.contains('location', case=False)
    loc = df[loc]


    ### Locoation happens only once; add to area dataframe
    area = area.append(loc, ignore_index = False)
    area = area.append(rooms, ignore_index = False)
    print(hrule,"Rows with \'area, more than 2 rooms, and location\'\n\n", area)
    print(Hrule)


    ### Find joint and conditional probabilities of these subdatasets
    ###
    print(hrule, "joint probability of subset where \'room\' is spoken\n\n")
    joint_room = get_joint_probability(room, 'questionLabels')
    print(hrule, "conditional probability of subset where \'room\' is spoken\n\n")
    cond_room = get_conditional_probability(room, 'questionLabels', 'qPhrase')

    sys.exit()
    joint_area = get_joint_probability(area, 'questionLabels')
    cond_area = get_conditional_probability(area, 'questionLabels', 'qPhrase')












    print(df['questionLabels_nm'].value_counts())
    rdata = replaceTerms(df)
    print(rdata['questionLabels_nm'].value_counts())

    ### Use one-hot encoding to find correlations between labels and 
        # word utterances from raw text
    o_qnm = pandas.get_dummies(rdata[['questionLabels_nm']])
    o_qW = pandas.get_dummies(rdata[['qWord']])

    X = pandas.concat([o_qW, o_qnm], axis = 1)
    y = df['score']
    regression = linear_model.LinearRegression()
    myReg = regression.fit(X, y)
    print(X.head(10))
    print(y.head(10))

    ### Correlate this 







'''
def cramer(q):
    ### Cramer's V
    #create 2x2 table
    data = numpy.array([[6,9], [8, 5], [12, 9]])

    #Chi-squared test statistic, sample size, and minimum of rows and columns
    X2 = stats.chi2_contingency(data, correction=False)[0]
    n = numpy.sum(data)
    minDim = min(data.shape)-1

    #calculate Cramer's V
    V = numpy.sqrt((X2/n) / minDim)

    #display Cramer's V
    print(V)


    X2 = stats.chi2_contingency(q, correction=False)[0]
    n = numpy.sum(q)
    minDim = min(q.shape)-1
    V = numpy.sqrt((X2/n)/minDim)
    print(V)
'''
###############################################################################
##### PROGRAM STARTS HERE
###############################################################################

###################################################################
### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*80 + "\n")
Hrule = ("\n" + "="*80 + "\n")

### Set number of rows to display in output:
HEAD = 20

###################################################################
### Use this block to clean data before using this file, else use next block.
### Read in the Data:
'''
file = "../data/doNotCommit2_HSR_raw.csv"
print("\n\n\t...reading in file...", file, "\n", hrule)
### Start Cleaning Process from main()
print("\n\n\t...cleaning the data...", hrule)
data = ctd.main(file)
### Verify
print(hrule, "\nChecking head(10) of myCleanedData:\n\n", data.head(10), hrule)
time.sleep(1)

'''
### Read in the data
file = "../data/doNotCommit2_HSR_readyForUse.csv"
print(hrule, "\t...reading in file...", file, "\n")
data = pandas.read_csv(file)
print(hrule, "\nChecking head(3) of myCleanedData:\n\n", data.head(3), hrule)


rdata = data.copy(deep = True) # To become a less-granular dataframe.
### Run the program the first time.
main(data)
HSR_main(data)

print(Hrule, "\t\t\tEnd of Program", Hrule)

###############################################################################

