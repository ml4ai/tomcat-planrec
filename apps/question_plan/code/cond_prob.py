
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


###############################################################################
### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*76 + "\n")
Hrule = ("\n" + "="*76 + "\n")
###############################################################################
### Use this block to clean data before using this file, else use next block.
'''
### Read in the Data:
file = "../data/doNotCommit_HSR_raw.csv"
### Start Cleaning Process from main()
data = ctd.main(file)
### Verify
print(Hrule, "\nChecking myCleanedData:\n\n", data.head(10), Hrule)
'''


### Read in the data
data = pandas.read_csv("../data/doNotCommit_HSR_readyForUse.csv")

###############################################################################

### Examine Data 

### Set some display options
pandas.set_option('display.max_rows', 200)
pandas.set_option('display.float_format', '{:.2}'.format)

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
    count = 0
    print(Hrule)

    for d in df:
        print("\n", d)
        print(df[d].value_counts().head(50))
        count += 1 
        print("-"*10, "Total Counts =", count, "-"*10, "\n")

#valCount(catData)




### Subset by group using a function
def subset_df(df, num):
    '''
    Purpose: Takes in any data frame and returns all rows that have label instances of
             more than value of 'num'.

             Because of the many 1-to-1 labels, we can filter for label instances that take
             place 1, 2, 3 or 4 times. Below we create subsets of the data for the number of
             instances per label, respectively. Each subset creates a value count, grouped
             by abstractLabels, then by question labels. A second subset takes the first
             subset and returns a normalized count.

    Input:   dataframe, number of instances to filter labels by
    Output:  dataframe subset by value count, dataframe subset by normalized count

    '''

    print(df.shape, "before subsetting\n")
    df = df.groupby("questionLabels").filter(lambda g: (g.name != 0) and
            (g.questionLabels.size > num))

    df = df.groupby("abstractLabels").filter(lambda g: (g.name != 0) and
            (g.questionLabels.size > num))

    print(df.shape, "after subsetting\n")

    ### Remember to return a copy of the dataframe without value counts
        # or normalized counts. Below are the other respective versions.

    ### Create Separate DataFrame that includes value counts
    ### Make deep copy or else the rest of this code won't work because the
        # value_counts() turns the data into series.
    # Convert resulting series to a dataframe before returning

    df_val = df.copy(deep = True)
    df_norm = df.copy(deep = True)

    df_val = df_val.groupby("abstractLabels")["questionLabels"].value_counts().head(200)
    df_val = df_val.to_frame()

    df_norm = df_norm.groupby("abstractLabels")["questionLabels"].value_counts(normalize = True).head(200)
    df_norm = df_norm.to_frame()

    return df, df_val, df_norm




#print(hrule, "All instances:\n", catData.groupby("abstractLabels")["questionLabels"].value_counts().head(200))
subCat1_df, subCat1_df_val, subCat1_df_norm = subset_df(catData, 1)
subCat2_df, subCat2_df_val, subCat2_df_norm = subset_df(catData, 2)
subCat3_df, subCat3_df_val, subCat3_df_norm = subset_df(catData, 3)
subCat4_df, subCat4_df_val, subCat4_df_norm = subset_df(catData, 4)

print(Hrule, subCat3_df, Hrule)
print(Hrule, subCat3_df_val, Hrule)
print(Hrule, subCat3_df_norm, Hrule)

print(type(subCat3_df))
print(type(subCat3_df_val))
print(type(subCat3_df_norm))



def cond_prob(df):
    '''
    Create Contingency Chart and Calculate Conditional Probabilities of
    Question Labels, given the Abstract Label
    '''
    df_table = pandas.crosstab(index=df["abstractLabels"], columns=df["questionLabels"], margins = True)

    print(hrule, "Contingency Table\n", df_table, Hrule)

    return df_table

### Send a subset dataframe, not subset value_counts or normalized frame
cond_prob(subCat3_df)


###############################################################################
'''
figureName = (ggplot(data,
                     aes("qWord",
                         "questionLabels",
                         fill = "StartSeconds")) +
              geom_tile())
#              facet_wrap("~video") # tilda goes inside quotes now.

print(figureName)

'''




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
