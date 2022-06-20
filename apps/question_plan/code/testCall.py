
'''
--------------------------------------------------------------------------
This code will not run from the tomcat-planrec repo until I upload the csv data.
--------------------------------------------------------------------------

Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 20 June 2022
Last Updated: 20 June 2022

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
    2. asdf
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
import matplotlib.pyplot as pyplot
from plotnine import *

### Will not work from repo until I upload dataset
import cleanTheData as ctd


'''
Functions in File:
    1. getRawData(filename)
        * Reads in csv file. See note on line 2.
        * Returns dataframe with features of interest
    2. cleanLabels(df, dirtyCol)
        * Calls out to 3 Functions:
    3.     * convert_datetime_integer(column)
             * converts timestamps to total seconds
    4.     * findColumn(df)
             * locates other columns that need conversions
    5.     * alphabetizeObjects(column)
             * splits parts of speech, checks for missing modifiers,
               checks for missing nouns, reorders labels for convention,
               and returns cleaned columns for all labels sent in the
               verbObjectObject format.
'''
###############################################################################
### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*76 + "\n")
Hrule = ("\n" + "="*76 + "\n")
###############################################################################

### Read in the Data:
file = "../data/doNotCommit_HSR_raw.csv"

### Start Cleaning Process from main()
data = ctd.main(file)

### Verify
print(Hrule, "\nChecking myCleanedData:\n\n", data.head(10), Hrule)

###############################################################################

### Examine Data 
pandas.set_option('display.max_rows', 40)

#print(hrule, "Describe Numerical Data:\n", data.describe(), hrule)
#print(hrule, "Describe Categorial Data:\n", data.describe(include=object), hrule)

### Subset the Data
numData = data[["video", "obsNum", "regular", "critical", "score",
                "StartSeconds"]]
catData = data[["question_verbatim", "htns", "abstractLabels", "causeLabels",
                "questionLabels", "effectLabels", "qWord", "qPhrase", "auxVerb", "actionVerb"]]



### All Unique Values of a Column
def unique(df):

    for d in df:
        print(hrule, d, hrule)
        print(df[d].unique())
        print(Hrule)

def valCount(df):
    print(Hrule)
    for d in df:
        print("\n", d)
        print(df[d].value_counts().head(20))

#valCount(catData)




### Subset by group using a function
def subset_df(df):
    df = df.groupby("questionLabels").filter(lambda g: (g.name != 0) and (g.questionLabels.size >= 2))
    print(df.shape)

    df = df.groupby("actionVerb").filter(lambda g: (g.name != "nil"))
    print(df.shape)

    df = df.groupby("abstractLabels").filter(lambda g: (g.name != 0) and (g.questionLabels.size >= 2))
    print(df.shape)
    time.sleep(3)
    return df

subCat_df = subset_df(catData)

valCount(subCat_df)
#####


figureName = (ggplot(data,
                     aes("qWord",
                         "questionLabels",
                         fill = "StartSeconds")) +
              geom_tile())
#              facet_wrap("~video") # tilda goes inside quotes now.

print(figureName)





###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
###############################################################################
