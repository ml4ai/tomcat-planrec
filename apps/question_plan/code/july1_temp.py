'''
--------------------------------------------------------------------------
This code will not run from the tomcat-planrec repo until I upload the csv data.
--------------------------------------------------------------------------

Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 20 June 2022
Last Updated: 1 July 2022

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
import datetime
import matplotlib.pyplot as pyplot

### Uncomment if you plan to use plotnine
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
def get_cond_prob(df, colA, colB, HEAD, title):
    '''
    Purpose:
    Input:
    Output:

    '''
    print(Hrule, "start of get_cond_prob()")
    #print(df.shape, "before subsetting\n")
    print(hrule, "\n\tcolA:", colA, "\n\tcolB:", colB, "\n")
    '''
    DECIDE IF I WANT TO CONSIDER FREQUENCY FOR LABELS.
    There are still too many 1-to-1 labels from a|q and q|a

    df = df.groupby(colB).filter(lambda g: (g.name != 0) and
            (g.colB.size > HEAD))

    df = df.groupby(colA).filter(lambda g: (g.name != 0) and
            (g.colA.size > HEAD))
    '''

    #print(df.shape, "after subsetting\n")

    ### Remember to return a copy of the dataframe without value counts
        # or normalized counts. 

    ### Make deep copy or else the rest of this code won't work because the
        # value_counts() turns the data into series. Convert resulting series to a dataframe before returning

    df_norm = df.copy(deep = True)
    #print(df_norm.shape, "after subsetting and deep copy\n")
    df_norm = df_norm.groupby(colA).value_counts(normalize = True).to_frame()
    df_norm.reset_index(inplace = True)
    df_norm.rename(columns={df_norm.columns[-1]: "conditional_probability" }, inplace = True)
#    print(Hrule, "\n\tConditional Probability of\n", title, "\n", hrule, df_norm, "\n\n", hrule)
    print(df_norm.shape, "after subsetting and deep copy and groupby", hrule)
    print(df_norm.head(5))
    sys.exit()

    return df, df_norm

###############################################################################
###############################################################################

def get_joint_prob(df, column, newColumn, HEAD):
    '''
    Purpose: Find Joint Probability of given column
    Input:
    Output: dfnf= DataFrame that is Normalized and formatted as Frame
            sparse = all rows in dfnf whose normalized values <= 0.01
            common = all rows in dfnf whose normalized values > 0.1

    '''
    print(Hrule)
    print(hrule, "start of get_joint_probability()", hrule)
    print(df.shape, "before subsetting\n")

    ### Make deep copy of dataframe and extract abstraction labels
    df_norm = df.copy(deep = True)
    df_norm = df_norm[column].value_counts(normalize=True).head(HEAD)
    # Turn into a dataframe since value_counts() converts to a series.
    dfnf = df_norm.to_frame()

    # Source for help: https://stackoverflow.com/questions/25457920/convert-row-names-into-a-column-in-pandas
    dfnf.index.name = 'newhead'
    dfnf.reset_index(inplace=True)

    ### Calculate the JOINT Probability
    dfnf.columns =[newColumn, 'probability']
    print(hrule, "Verify shape and data types of subdataframe:\n", 
            "\nShape:", dfnf.shape, "\nDataTypes:\n", dfnf.dtypes)

    ### Attempt to get POS from Abstract Labels
    #TODO: Do I need this line?  dfnf = ctd.cleanLabels(dfnf, newColumn)
    print(hrule, dfnf, hrule)

    ### Filter subset of data into sparse and common, based on probability
    sparse = dfnf.copy(deep = True)
    sparse = sparse[sparse.probability <= 0.01]
    common = dfnf.copy(deep = True)
    common = common[common.probability >= 0.1]

    return dfnf, sparse, common

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
    catData = data[["htns", "abstractLabels", "question_verbatim",
                    "abstractLabels_v", "abstractLabels_nm", "causeLabels",
                    "questionLabels", "questionLabels_v", "questionLabels_nm",
                    "effectLabels", "qWord", "qPhrase", "auxVerb", "actionVerb"]]

    ### This block is an introduction
    '''
    This next line shows entropy for all instances of labels for questions and
    abstractions. This is not helpful for generalizations but can still be used for
    investigating variation, probability given other joint conditions, and when
    granularity does or does not matter.

    ### Commentary to self
    #Compare Information Entropy-- a lot of these labels degenerate into one-to-one
    #information that is not helpful. Is this because of the labels themselves or
    #because there isn't enough data?

    #TODO: Annotate another set of videos after pre-registration results are
    #completed

    #Get marginal probabilities of labels:
    #    First send abstract labels to find mid-level intentions and probabilities.
    #    Second send in question laels to find ground-level intent and probability.
    #    Then feed them into a contingency table to see frequencies.

    #    As of 21 June, simply write notes in comments, in this document, about why
    #    I am going to subsume certain labels.


    # This block finds marginal probs, converts back into dataframe, then I use
    # the new dataframe to send to conditional and then I get two full columns
    # back as a new dataframe.

    # This is different than the blocks below in making the to_frame more
    # explicit but I don't know which approach is better.
    '''

    ### First send abstract labels to find mid-level intentions and probabilities.
    abs_dfnf, abs_sparse, abs_common = get_joint_prob(catData, "abstractLabels", "intention", 400)

    ### Second send in question laels to find ground-level intent and probability.
    q_dfnf, q_sparse, q_common = get_joint_prob(catData, "questionLabels",
    "questionLabels_v", 400)


    ###   TODO: this main() is an abomination that needs to be cleaned. With a fresh
    ###   brain due to vacation, I intend to finish this today. 1 July 2022.

    ### Now look at sparse, normalized categorical labels to see what to combine:
#    print(hrule, "Sparse Contingency Matrices for Purpose of Subsuming Labels",
#            hrule)
#
#    contingency_tables(abs_sparse, "intentions_v", "intentions_nm")
#    contingency_tables(q_sparse, "questionLabels_v", "questionLabels_nm")

    ### Now print conditional probabilities
    #TODO: Decide whether I should use different variables. Not sure for now.
    condProb_cat, condProb_cat_norm = get_cond_prob(catData,
            "abstractLabels", "questionLabels", 0, "Abstract Labels that Show Intention")

    print(hrule)

    ### Conditional Probabilities of Labels:
    ### Send dataframe with marginal probability to get conditional with
        ### marginal in same frame.
    condProb_q, condProb_q_norm = get_cond_prob(q_dfnf,
            "questionLabels_v", "questionLabels_nm", 0, "Question Labels that Capture Action or Intention")
    ### Rearrange columns for easier reading:
    #TODO: automate the rearrangement of columns like this in function


    # Rearrange the columns
    condProb_q_norm = condProb_q_norm[['questionLabels',
        'questionLabels_v', 'questionLabels_nm', 'joint_probability',
        'conditional_probability']]
    print(hrule, condProb_q_norm.head(5))






    ### Send dataframe with marginal probability to get conditional with
        ### marginal in same frame.
    condProb_abs, condProb_abs_norm = get_cond_prob(abs_dfnf,
            "intentions_v", "intentions_nm", 0, "Abstract Labels that Show Intention")
    ### Rearrange columns
    condProb_abs_norm = condProb_abs_norm[['intentions','intentions_v',
        'intentions_nm', 'joint_probability', 'conditional_probability']]
    print(hrule, condProb_abs_norm.head(5))


#######################################################################################################
    ### Print marginal probabilities



    #### Print Conditional Probabilities
    ### Print Components in order to find Likelihoods
    comps = catData[["abstractLabels", "abstractLabels_v", "abstractLabels_nm",
        "questionLabels", "questionLabels_v", "questionLabels_nm"]]
   # print(comps.head(5), hrule)

#    print(hrule, "P(abstractLabels_v)\n\n",
#            comps["abstractLabels_v"].value_counts(normalize = True).head(200))
#    print(hrule, "P(abstractLabels_nm)\n\n",
#            comps["abstractLabels_nm"].value_counts(normalize = True).head(200))
#    print(hrule, "P(questionLabels_v)\n\n",
#            comps["questionLabels_v"].value_counts(normalize = True).head(200))
#    print(hrule, "P(questionLabels_nm)\n\n",
#            comps["questionLabels_nm"].value_counts(normalize = True).head(200))

#    print(hrule, "Value Counts for ASK\n\n")
#    ask = comps['questionLabels'].str.contains('ask')
#    print(comps[ask])

    #### Conditional Probabilities of Components
    #print(hrule, "P(a_v | a_nm)\n",
    #        comps.groupby("abstractLabels_nm").value_counts(normalize =
    #            True).head(200))
    #print(hrule, "P(a_nm | a_v)")
    #print(hrule, "P(q_v | q_nm)")
    #print(hrule, "P(q_nm | q_v)")
    #print(hrule, "P(q_v |a_v )")
    #print(hrule, "P(a_nm |q_nm )")
    #print(hrule, "P(q_nm |a_nm )")


#######################################################################################################
    ### Print Probabilites of questions and questions phrases or question words
    q = catData[["questionLabels", "questionLabels_v", "questionLabels_nm",
        "qWord", "qPhrase", "actionVerb"]]
    print(q.head(5))

    ### Marginal
    print(hrule,"\nMarginal Probability of Question Phrase\n\n", q["qPhrase"].value_counts(normalize =
        True).head(200), "\n")


#######################################################################################################

### Commentary to self: Same as large block above but more concise
    ### Because I want no 1 to 1 labels for abstract and question, it would be
       # nice to have higher probability of q|a, and lower p(a|q). Below are
       # some replacements that I am using to fix some of these:
    #This block is basically the same stuff as above but written more concise

    def tryReplace(df, old, new):
        # Replaces in entire dataframe for all columns
        print(hrule, "replace", old, "with", new, "\n")
        df = df.replace(old, new, regex=True)
        return df

    def tryColReplace(df, col, old, new):
        # Replaces in given column
        print(hrule, "replace", old, "with", new, "\n")
        df[col] = df[col].replace(old, new, regex=True)
        return df

    def reMarg(df, colA, colB):
        print(hrule)
        aq1 = df.groupby(colA).value_counts(normalize=True).head(200).to_frame()
        #aq1 = df.groupby("questionLabels_v").value_counts(normalize = True).head(200).to_frame()
        aq1.reset_index(inplace=True)
        aq1.columns =[colA, colB, 'probability']
        print(aq1)
        return aq1

    def reLike(df):
        print(hrule, "P(qnm | qv)\n\n")
        aq1 = df.groupby("questionLabels_v").value_counts(normalize = True).head(200).to_frame()
        aq1.reset_index(inplace=True)
        aq1.columns =['questionLabels_v', 'questionLabels_nm', 'probability']
        print(aq1)
        return aq1


## delete when done: def get_cond_prob(df, colA, colB, HEAD, title):
## delete when done: def get_joint_prob(df, column, newColumn, HEAD):

    testdf = catData[['questionLabels_v', 'questionLabels_nm']]
    print(hrule, "\n\n\t Marginal Probability of Question Verbs\n\n", testdf['questionLabels_v'].value_counts(normalize =
        True).head(200), "\n\n\t End of p(qv)\n\n")
    print(hrule, "\n\n\t Marginal Probability of Question Objects\n\n", testdf['questionLabels_nm'].value_counts(normalize =
        True).head(200), "\n\n\t End of p(q_nm)\n\n")
    marginalized_testdf1 = get_joint_prob(testdf, "questionLabels_nm", "q_nm", 200)
    print(marginalized_testdf1)

    print(hrule, "\n\n\t Conditional Probability of (qv | qnm) \n\n", testdf.groupby("questionLabels_nm").value_counts(normalize =
        True).head(200).to_frame(), "\n\n\t End of p(qv | qnm)\n\n")
##### #####  ##### #####  ##### #####  ##### ##### 

    test2 = catData[['questionLabels_v', 'qPhrase']]
    print(hrule, "\n\n\t Conditional Probability of (qv | qPhrase) \n\n",
            test2.groupby("questionLabels_v").value_counts(normalize =
        True).sort_index().head(200).to_frame(), "\n\n\t End of p(qv | qPhrase)\n\n")

    reMarg(test2, "questionLabels_v", "qPhrase")
    reMarg(test2, "qPhrase", "questionLabels_v")
    plot_df_fill(test2, "questionLabels_v", "qPhrase", "probability")

 ##### #####  ##### #####  ##### #####  ##### ##### 
    test3 = catData[['questionLabels_nm', 'qPhrase']]
    print(hrule, "\n\n\t Conditional Probability of (qnm | qPhrase) \n\n",
            test3.groupby("questionLabels_nm").value_counts(normalize =
        True).sort_index().head(200).to_frame(), "\n\n\t End of p(qnm | qPhrase)\n\n")

    reMarg(test3, "questionLabels_nm", "qPhrase")
    reMarg(test3, "qPhrase", "questionLabels_nm")

 ##### #####  ##### #####  ##### #####  ##### #####


    #reLike(testdf)

##### #####  ##### #####  ##### #####  ##### #####
##### #####  ##### #####  ##### #####  ##### #####
    cramer(q)
#    testdf = tryReplace(testdf, "Room", "Location")
#    testdf = tryReplace(testdf, "notice", "prioritize")
#    testdf = tryReplace(testdf, "confirm", "clarify")
#    testdf = tryReplace(testdf, "Knowledge", "Information")
#    testdf = tryReplace(testdf, "wakeCritical", "collaborateCriticalWake")
#    testdf = tryColReplace(testdf, "abstractLabels", "requestCriticalWake",
#            "collaborateCriticalWake")
#    reMarg(testdf)
#    reLike(testdf)

    return data # end of main()

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
Hrule = ("\n" + "#"*80 + "\n")

### Set number of rows to display in output:
HEAD = 20

###################################################################
### Use this block to clean data before using this file, else use next block.
### Read in the Data:
file = "../data/doNotCommit2_HSR_raw.csv"
print("\n\n\t...reading in file...", file, "\n", hrule)
### Start Cleaning Process from main()
print("\n\n\t...cleaning the data...", hrule)
data = ctd.main(file)
### Verify
print(hrule, "\nChecking head(10) of myCleanedData:\n\n", data.head(10), hrule)
time.sleep(3)

'''
### Read in the data
file = "../data/doNotCommit2_HSR_readyForUse.csv"
print(hrule, "\t...reading in file...", file, "\n")
time.sleep(1)
data = pandas.read_csv(file)
print(hrule, "\nChecking head(10) of myCleanedData:\n\n\n", data.head(10), hrule)

'''


### Run the program the first time.
main(data)


### Since I want to find a way to use probabilities and tables to see what
    # be subsumed, I need to do at base level. For now, I'll rerun main after
    # I replace all substrings with desired replacements.
    # Source: https://sparkbyexamples.com/pandas/pandas-replace-substring-in-dataframe/

### replace "confirm" with "clarify"
#TODO: Should confirm remain in question and NOT abstract??? Start here.



print(Hrule, "\t\t\tEnd of Program", Hrule)

###############################################################################

