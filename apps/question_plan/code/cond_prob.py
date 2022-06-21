
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


Sources used considerably while learning to use Pandas, though none of their
code was used directly for the development of this program:

    https://towardsdatascience.com/8-ways-to-filter-a-pandas-dataframe-by-a-partial-string-or-pattern-49f43279c50f

    https://re-thought.com/pandas-value_counts/

    https://towardsdatascience.com/9-pandas-value-counts-tricks-to-improve-your-data-analysis-7980a2b46536


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
#from plotnine import *

### Will not work from repo until I upload dataset
import cleanTheData as ctd


###############################################################################

### All Unique Values of a Column
def unique(df):
    for d in df:
        print(hrule, d, hrule)
        print(df[d].unique())
        print(Hrule)
###############################################################################

def valCount_df(df, num):
    '''
    Counts of all values for all columns of dataframe. 
    'num' indicates the number of rows to be displayed in dataframe.
    '''

    count = 0
    print(Hrule)

    for d in df:
        print("\n", d)
        print(df[d].value_counts().head(num))
        count += 1 
        print("-"*10, "Total Counts =", count, "-"*10, "\n")



def valCount_col(col, num):
    '''
    Counts all of the values for a specific column in a data frame.
    'num' indicates the number of rows to be displaced in this output.
    '''
    print(hrule, col.value_counts().head(num),
            hrule, col.value_counts(normalize = True).head(num))


###############################################################################

### Group-by using a function
def groupBy_df(df, num):
    '''
    Do not use a subsetting function. This is groupby that returns a
    wide-verses-long dataframe, which I like for the investigation of concept
    hierarchies, not necessarily a subset.

    For subsetting, use the sub-set_df() function.

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
    print(Hrule, "start of groupBy_df()", hrule)
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
    print(df_norm.shape, "after subsetting and deep copy\n")

    df_val = df_val.groupby("abstractLabels")["questionLabels"].value_counts().head(400)
    df_val = df_val.to_frame()
    #df_val = pandas.DataFrame(df_val)

    df_norm = df_norm.groupby("abstractLabels")["questionLabels"].value_counts(normalize
            = True).head(400)
    print(df_norm.shape, "after subsetting and deep copy and groupby\n")

    #df_norm = df_norm.to_frame()
    df_norm = pandas.DataFrame(df_norm)
    print(df_norm.shape, "after subsetting and deep copy, groupby and df\n")
    print(hrule, "end of groupBy_df()", Hrule)
    return df, df_val, df_norm

###############################################################################
###############################################################################

def intent_probability(df, num):
    '''
    Purpose: Takes in any data frame and returns all rows that have label instances of
             more than value of 'num'.

    Input:   dataframe, number of rows to display
    Output:

    '''
    print(Hrule, "start of intent_probability()", hrule)
    print(df.shape, "before subsetting\n")
    print(hrule, "\nUse Abstractions to Capture Intention of Player.\n"
            "This label captures the question utterance at a higher level and\n"
            "considers the cause and effect of such a question utterance.\n")

    ### Make deep copy of dataframe and extract abstraction labels
    df_norm = df.copy(deep = True)
    df_norm = df_norm["abstractLabels"].value_counts(normalize=True).head(num)
    # Turn into a dataframe since value_counts() converts to a series.
    dfnf = df_norm.to_frame()

    ### Conversions need to be reshaped. Abstractions need to be taken from
        # row names into their own column. Define as Intention.
        # Define normalized value counts as probability of marginal probability
        # of the intention being the intention, regardless of question asked.
        # Source for help: https://stackoverflow.com/questions/25457920/convert-row-names-into-a-column-in-pandas

    dfnf.index.name = 'newhead'
    dfnf.reset_index(inplace=True)
    dfnf.columns =['intention', 'probability']
    print(hrule, dfnf)
    print(hrule, "Verify shape and data types of subdataframe:\n", 
            "\nShape:", dfnf.shape, "\nDataTypes:\n", dfnf.dtypes)


    ### Filter subset of data into sparse and common, based on probability
    sparse = dfnf.copy(deep = True)
    sparse = sparse[sparse.probability <= 0.01]
    print(hrule, "Sparse:\n", sparse)

    common = dfnf.copy(deep = True)
    common = common[common.probability >= 0.1]
    print(hrule, "Common:\n", common)
#df = df[df.column_name != value]


    print(hrule, "end of intent_probability()", Hrule)

#    return df, df_val, df_norm

###############################################################################
##########################################################

def cont_table(df):
    '''
    Create Contingency Chart and Calculate Conditional Probabilities of
    Question Labels, given the Abstract Label
    '''
    df_table = pandas.crosstab(index=df["abstractLabels"], columns=df["questionLabels"], margins = True)

    print(hrule, "Contingency Table\n", df_table, Hrule)

    return df_table

###############################################################################





###############################################################################

def print_df(df):
    print(hrule, df, hrule)

def plot_df_fill(df, a, b, c):
    figure = (ggplot(df,
                    aes(a, b,
                        fill = c)) +
              geom_tile())
    print(figure)





###############################################################################
##### PROGRAM STARTS HERE
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
pandas.set_option('display.max_rows', 400)
pandas.set_option('display.float_format', '{:.2}'.format)
#print(hrule, "Describe Numerical Data:\n", data.describe(), hrule)
#print(hrule, "Describe Categorial Data:\n", data.describe(include=object), hrule)

### Subset the Data
numData = data[["video", "obsNum", "regular", "critical", "score",
                "StartSeconds"]]
catData = data[["question_verbatim", "htns", "abstractLabels", "causeLabels",
                "questionLabels", "effectLabels", "qWord", "qPhrase", "auxVerb", "actionVerb"]]

### Get a feel for categorical Data:
#valCount(catData, 200)

### Send a subset dataframe, not subset value_counts or normalized frame
'''
This next line shows entropy for all instances of labels for questions and
abstractions. This is not helpful for generalizations but can still be used for
investigating variation, probability given other joint conditions, and when
granularity does or does not matter.
'''
#print(hrule, "All instances:\n", catData.groupby("abstractLabels")["questionLabels"].value_counts().head(200))
groupBy_catData_df, groupBy_Data_df_val, groupBy_catData_df_norm = groupBy_df(catData, 0)
#groupBy_subCat1_df, groupBy_Cat1_df_val, groupBy_Cat1_df_norm = groupBy_df(catData, 1)
#groupBy_subCat2_df, groupBy_Cat2_df_val, groupBy_Cat2_df_norm = groupBy_df(catData, 2)
#groupBy_subCat3_df, groupBy_Cat3_df_val, groupBy_Cat3_df_norm = groupBy_df(catData, 3)
#groupBy_subCat4_df, groupBy_Cat4_df_val, groupBy_Cat4_df_norm = groupBy_df(catData, 4)
#cont_table(subCat3_df)


##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 
 ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 
  ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### ##### 

print(Hrule, "What Intentions Exist?", hrule)
#valCount_col(catData["abstractLabels"], 200)

'''
Compare Information Entropy-- a lot of these labels degenerate into one-to-one
information that is not helpful. Is this because of the labels themselves or
because there isn't enough data?

#TODO: Annotate another set of videos after pre-registration results are
completed

# TODO: Subsume some of these labels
'''


def subsumeLabels(df):
    print(hrule, "ready for subsuming\n", df, hrule)
    '''
    Many of these are above probability > 10% and several are at 100%

    First subsume anything less than 10% with filtering into a new
    dataframe to find the rules, then replace with a replace function.
    '''
    #temp_cleaned.to_csv("../data/temp_csv_folder/temp_ABC_"+dirtyCol+"_from_doNotCommit_Cleaned.csv")

   # df_sparse_to_subsume = pandas.DataFrame(df)
   # print(type(df))
   # print(type(df_sparse_to_subsume))
   # print(df_sparse_to_subsume.shape)
   # print(df_sparse_to_subsume.head())


#df = df[df.column_name != value]
    ### Filter all rows where the normalized value is less than 1 %
###############################################################################




intent_probability(catData, 400)
###############################################################################
###############################################################################
###############################################################################
