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


Sources to consider down the road:
    * Converting wide <-> long data for analysis vs visualization
        * https://www.statology.org/long-vs-wide-data/
'''


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
###############################################################################

def valCount_df(df, HEAD):
    '''
    Counts of all values for all columns of dataframe. 
    'HEAD' indicates the number of rows to be displayed in dataframe.
    '''
    print(Hrule)

    for d in df:
        print("\n", d)
        print(df[d].value_counts().head(HEAD))



def valCount_col(col, HEAD):
    '''
    Counts all of the values for a specific column in a data frame.
    'HEAD' indicates the number of rows to be displaced in this output.
    '''
    print(hrule, col.value_counts().head(HEAD),
            hrule, col.value_counts(normalize = True).head(HEAD))


###############################################################################

### Group-by using a function
def cond_prob_df(df, colA, colB, HEAD, title):
    '''
    Do not use a subsetting function. This is groupby that returns a
    wide-verses-long dataframe, which I like for the investigation of concept
    hierarchies, not necessarily a subset.

    For subsetting, use the sub-set_df() function.

    Purpose: Takes in any data frame and returns all rows that have label instances of
             more than value of 'HEAD'.

             Because of the many 1-to-1 labels, we can filter for label instances that take
             place 1, 2, 3 or 4 times. Below we create subsets of the data for the number of
             instances per label, respectively. Each subset creates a value count, grouped
             by abstractLabels, then by question labels. A second subset takes the first
             subset and returns a normalized count.

    Input:   dataframe, number of instances to filter labels by
    Output:  dataframe subset by value count, dataframe subset by normalized count

    '''
    #print(Hrule, "start of cond_prob_df()")
    #print(df.shape, "before subsetting\n")
    '''
    DECIDE IF I WANT TO CONSIDER FREQUENCY FOR LABELS. I STILL DON'T THINK THAT
    I DO.

    df = df.groupby(colB).filter(lambda g: (g.name != 0) and
            (g.colB.size > HEAD))

    df = df.groupby(colA).filter(lambda g: (g.name != 0) and
            (g.colA.size > HEAD))
    '''

    #print(df.shape, "after subsetting\n")

    ### Remember to return a copy of the dataframe without value counts
        # or normalized counts. Below are the other respective versions.

    ### Create Separate DataFrame that includes value counts
    ### Make deep copy or else the rest of this code won't work because the
        # value_counts() turns the data into series.
    # Convert resulting series to a dataframe before returning

    df_norm = df.copy(deep = True)
    #print(df_norm.shape, "after subsetting and deep copy\n")

    df_norm = df_norm.groupby(colA).value_counts(normalize = True).to_frame()
    df_norm.reset_index(inplace = True)
    df_norm.rename(columns={ df_norm.columns[3]: "marg_prob" }, inplace = True)
    df_norm.rename(columns={ df_norm.columns[4]: "cond_prob" }, inplace = True)


    #print(df_norm.shape, "after subsetting and deep copy, groupby and df\n")



#    print(Hrule, "\n\tConditional Probability of\n", title, "\n", hrule, df_norm, "\n\n", hrule)
    print(df_norm.shape, "after subsetting and deep copy and groupby\n")

    return df, df_norm

###############################################################################
###############################################################################

def marginal_probability(df, column, newColumn, HEAD):
    '''
    Purpose: Takes in any data frame and returns all rows that have label instances of
             more than value of 'HEAD'.

    Input:   dataframe, number of rows to display
    Output: dfnf= DataFrame that is Normalized and formatted as Frame
            sparse = all rows in dfnf whose normalized values <= 0.01
            common = all rows in dfnf whose normalized values > 0.1

    '''
    print(Hrule)
#    print(hrule, "start of intent_probability()", hrule)
#    print(df.shape, "before subsetting\n")
#    print(hrule, "\nUse Abstractions to Capture Intention of Player.\n"
#            "This label captures the question utterance at a higher level and\n"
#            "considers the cause and effect of such a question utterance.\n")

    ### Make deep copy of dataframe and extract abstraction labels
    df_norm = df.copy(deep = True)
    df_norm = df_norm[column].value_counts(normalize=True).head(HEAD)
    # Turn into a dataframe since value_counts() converts to a series.
    dfnf = df_norm.to_frame()

    ### Conversions need to be reshaped. Abstractions need to be taken from
        # row names into their own column. Define as Intention.
        # Define normalized value counts as probability of marginal probability
        # of the intention being the intention, regardless of question asked.
        # Source for help: https://stackoverflow.com/questions/25457920/convert-row-names-into-a-column-in-pandas

    dfnf.index.name = 'newhead'
    dfnf.reset_index(inplace=True)
    dfnf.columns =[newColumn, 'probability']
#    print(hrule, dfnf)
#    print(hrule, "Verify shape and data types of subdataframe:\n", 
#            "\nShape:", dfnf.shape, "\nDataTypes:\n", dfnf.dtypes)

    ### Attempt to get POS from Abstract Labels
    dfnf = ctd.cleanLabels(dfnf, newColumn)
#    print(hrule, dfnf, hrule)

    ### Filter subset of data into sparse and common, based on probability
    sparse = dfnf.copy(deep = True)
    sparse = sparse[sparse.probability <= 0.01]
#    print(hrule, "Sparse:\n", sparse)

    common = dfnf.copy(deep = True)
    common = common[common.probability >= 0.1]
#    print(hrule, "Common:\n", common)

#    print(hrule, "end of intent_probability()", hrule)

    return dfnf, sparse, common

###############################################################################

def plot_df_fill(df, a, b, c):
    '''
    This function uses R's ggplot() grammar, built on matplotlib

    Input: dataframe, independent variable, dependent variable, categorical var
    Output: any visualization that uses "fill" instead of "color"
    '''
    #TODO: make this more functional for choice in tile, bar, col
    #TODO: duplicate this function for color command: point, line, area
    figure = (ggplot(df,
                    aes(a, b,
                        fill = c)) +
              geom_tile())
    print(figure)


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
    #print(hrule, "Describe Numerical Data:\n", data.describe(), hrule)
    #print(hrule, "Describe Categorial Data:\n", data.describe(include=object), hrule)

    ### Subset the Data
    numData = data[["video", "obsNum", "regular", "critical", "score",
                    "StartSeconds"]]
    catData = data[["htns", "abstractLabels",
                    "abstractLabels_v", "abstractLabels_nm", "causeLabels",
                    "questionLabels", "questionLabels_v", "questionLabels_nm",
                    "effectLabels", "qWord", "qPhrase", "auxVerb", "actionVerb"]]


    '''
    This next line shows entropy for all instances of labels for questions and
    abstractions. This is not helpful for generalizations but can still be used for
    investigating variation, probability given other joint conditions, and when
    granularity does or does not matter.

    Get a feel for categorical Data. 
    '''


    '''
    Compare Information Entropy-- a lot of these labels degenerate into one-to-one
    information that is not helpful. Is this because of the labels themselves or
    because there isn't enough data?

    #TODO: Annotate another set of videos after pre-registration results are
    completed

    Get marginal probabilities of labels:
        First send abstract labels to find mid-level intentions and probabilities.
        Second send in question laels to find ground-level intent and probability.
        Then feed them into a contingency table to see frequencies.

        As of 21 June, simply write notes in comments, in this document, about why
        I am going to subsume certain labels.
    '''
    ### First send abstract labels to find mid-level intentions and probabilities.
    abs_dfnf, abs_sparse, abs_common = marginal_probability(catData, "abstractLabels", "intention", 400)

    ### Second send in question laels to find ground-level intent and probability.
    q_dfnf, q_sparse, q_common = marginal_probability(catData, "questionLabels",
    "primitiveQuestion", 400)

    ### Now look at sparse, normalized categorical labels to see what to combine:
#    print(hrule, "Sparse Contingency Matrices for Purpose of Subsuming Labels",
#            hrule)
#
#    contingency_tables(abs_sparse, "intentions_v", "intentions_nm")
#    contingency_tables(q_sparse, "primitiveQuestions_v", "primitiveQuestions_nm")

    ### Now print conditional probabilities
    #TODO: Decide whether I should use different variables. Not sure for now.
    #condProb_cat, condProb_cat_norm = cond_prob_df(catData,
    #        "abstractLabels", "questionLabels", 0, "Abstract Labels that Show Intention")



    print(hrule)

    ### Conditional Probabilities of Labels:
    ### Send dataframe with marginal probability to get conditional with
        ### marginal in same frame.
    condProb_q, condProb_q_norm = cond_prob_df(q_dfnf,
            "primitiveQuestions_v", "primitiveQuestions_nm", 0, "Questin Labels that Capture Action or Intention")
    ### Rearrange columns for easier reading:
    #TODO: automate the rearrangement of columns like this in function
    condProb_q_norm = condProb_q_norm[['primitiveQuestions',
        'primitiveQuestions_v', 'primitiveQuestions_nm', 'marg_prob',
        'cond_prob']]
    print(hrule, condProb_q_norm)


    ### Send dataframe with marginal probability to get conditional with
        ### marginal in same frame.
    condProb_abs, condProb_abs_norm = cond_prob_df(abs_dfnf,
            "intentions_v", "intentions_nm", 0, "Abstract Labels that Show Intention")
    ### Rearrange columns
    condProb_abs_norm = condProb_abs_norm[['intentions','intentions_v', 'intentions_nm', 'marg_prob', 'cond_prob']]
    print(hrule, condProb_abs_norm)

#TODO:
    '''
    21 June: subsume confirm into clarify. Do at ground level of main dataframe.
    For now, just run the program a few times?
    '''
    return data # to rerun program from base level


###############################################################################
##### PROGRAM STARTS HERE
###############################################################################

###################################################################
### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*80 + "\n")
Hrule = ("\n" + "#"*80 + "\n")

### Set number of rows to display in output:
HEAD = 20

###################################################################
### Use this block to clean data before using this file, else use next block.
'''
### Read in the Data:
file = "../data/doNotCommit_HSR_raw.csv"
### Start Cleaning Process from main()
data = ctd.main(file)
### Verify
print(hrule, "\nChecking myCleanedData:\n\n", data.head(10), hrule)
'''

### Read in the data
rawData = pandas.read_csv("../data/doNotCommit_HSR_readyForUse.csv")

### Run the program the first time.
main(rawData)


### Since I want to find a way to use probabilities and tables to see what
    # be subsumed, I need to do at base level. For now, I'll rerun main after
    # I replace all substrings with desired replacements.
    # Source: https://sparkbyexamples.com/pandas/pandas-replace-substring-in-dataframe/

### replace "confirm" with "clarify"
#TODO: Should confirm remain in question and NOT abstract??? Start here.
    #### rawData = rawData.replace('confirm','clarify', regex=True)


print(Hrule, "\t\t\tEnd of Program", Hrule)

###############################################################################
###############################################################################
