"""
--------------------------------------------------------------------------
Purpose:
    This utility file calculates joint, marginal and conditional probabilities
    of categorical features.It also uses global or by-column substring
    replacement of labels to explore user-specified label granularity.

    As of 12 July 2022, this file does not use HSR data.

    This file assumes that data labels are in
    camel-case "verbObjectObject" form for most categorical labels.


Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Created:
    20 June 2022

Last Updated:
    12 July 2022

Affiliation:
    Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
    Adarsh Pyarelal, Head PI and Clayton T. Morrison, Co-PI
    School of Information, University of Arizona

--------------------------------------------------------------------------
File Dependencies:
    cleanTheData.py

Attributes of comments in file to be aware of:
    '###' Single-line comments for user.
    '#' Commands that can be uncommented. Most of these are either print
        statements for debugging or data exploration samples/ heads.

Functions in File:
     * replaceSubstring_Global(df, old, new)
     * get_joint_probability(df, colA)
     * get conditional_probability(df, colA, colB)
     * replaceTerms(df)
     * reclean(df, col, newCol)
     * contingency_tables(df, colA, colB)
     * investigate_ReplacedTerms(dataframe)
     * main(data)

Sources and references:
    1) https://towardsdatascience.com/8-ways-to-filter-a-pandas-dataframe-by-a-partial-string-or-pattern-49f43279c50f
    2) https://re-thought.com/pandas-value_counts/
    3) https://towardsdatascience.com/9-pandas-value-counts-tricks-to-improve-your-data-analysis-7980a2b46536
--------------------------------------------------------------------------
"""

import datetime
import matplotlib.pyplot as pyplot
import numpy
import pandas
import requests
import scipy.stats as stats
from sklearn import linear_model
import sys
import time

import cleanTheData as ctd

#--------------------------------------------------------------------------
### Set to true or false to run program for each desired dataframe.
ORIGINAL_DATAFRAME = True
REPLACED_DATAFRAME = True
#--------------------------------------------------------------------------


### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*80 + "\n")
Hrule = ("\n" + "="*80 + "\n")

def replaceSubstring_Global(df, old, new):
    """
    Purpose:
        Called from replaceTerms(df) to replace whole or part of substring.

    Args:
        df: Dataframe to receive global replacement of a term
        old: old term
        new: new term

    Returns:
        df: Updated dataframe with new term, global replacement
    """
    print("\treplace", old, "with", new)
    df = df.replace(old, new, regex=True)
    return df


def get_joint_probability(df, colA):
    """
    Purpose:
        Calculate the joint probability of a dataframe's column of interest.
        This function creates a data frame with probability column and works
        for categorical data.

    Args:
        df: Dataframe
        colA: Column that has feature of interest.

    Returns:
        dfa: Dataframe with joint_probability column
        common: updated dataframe with top 20 joint probabilities.
    """
    dfa = df[colA].value_counts(normalize = True).sort_values().to_frame()
    dfa.reset_index(inplace = True)
    dfa.columns = [colA, 'joint_probability']
    print("\nJoint Probability of", colA, "\n")
    print(dfa, hrule)
    ### Now get the conditional probability of colB, given colA and constrain
        #colA to be the top 20 joint probabilities:
    common = dfa.tail(20)
    print("\nJoint Probability (tail) of", colA, "\n", common, hrule)

    return dfa, common


def get_conditional_probability(df, colA, colB):
    """
    Purpose:
        Calculate the conditional probability of a dataframe's feature of
        interest, conditioned on another column of interest. This function
        creates a dataframe that has the conditional probabilities in a column
        and works with categorical data.

    Args:
        df: Dataframe
        colA: The conditioning feature.
        colB: Feature whose conditional proability is to be calculated,
            conditioned on colA.

    Returns:
        df1: Dataframe with conditional_probability column
    """
    df1 = df.groupby(colA).value_counts(normalize = True).to_frame()
    df1.reset_index(inplace = True)
    # next line solution from: https://www.codegrepper.com/code-examples/python/pandas+change+the+last+column+name
    df1 = df1.rename(columns={0: 'conditional_probability'})
    print("\n Conditional Probability \t P(", colB, "|", colA, ")\n")
    print(df1, hrule)

    return df1


def reclean(df, col, newCol):
    """
    Purpose:
        Recleans labels if substrings were replaced globally.

    Args:
        df: Dataframe with the original labels.
        col: Column of labels to be replaced and recleaned.
        newCol: New name of column to be returned.

    Returns:
        df: Dataframe with replaced and cleaned labels.
    """
    df = ctd.cleanLabels(df, col)
    df = df.rename(columns={col: newCol})
    return df



def replaceTerms(df):
    """
    Purpose:
        Replaces certain terms in the data to reduce granularity of labels.
        Commented-out commands have less impact in reducing number of labels
        that have the joint probability <= 0.0052 (count = 1 for this dataset).

        The purpose is not to resolve sparse dataframes, but to investigate
        probabilistic and causal reasoning of players.

    Args:
        df: The entire dataframe

    Returns:
        df: The entire dataframe with replaced terms.

    Example:
        To investigate the difference of intention of a specific room or a more
        general area, replace labels to see how conditional probabilities of
        the question label, given the intention differ. Then investigate the
        conditional probabilities of the intention, given the question label
        (with and without replacement of terms).

        In this example, 'room' means a specific room and 'location' means a
        group of rooms, area, or section. Labels are annotated accordingly. The
        conditional probabilities, as described above, do not significantly
        change when I replace 'room' with 'location', so I now use this
        function to replace label components appropriately.

        All replacements can be found within this function.

    Update:
        Additional justification of label replacement, as specified in the
        above examples come from bagOfWords.py when evauluating the tf.d with
        and without label replacement. Update July 6, 2002.
    """
    df = replaceSubstring_Global(df, "Room", "Location") # see notes above
    df = replaceSubstring_Global(df, "LocationInformation", "Location")
    df = replaceSubstring_Global(df, "InformationThreatroom", "Threatroom")
    df = replaceSubstring_Global(df, "confirm", "clarify")
    df = replaceSubstring_Global(df, "Marker", "Mark")
    df = replaceSubstring_Global(df, "askPlan", "collaborate")
    df = replaceSubstring_Global(df, "Stabilizedvictim", "Stabilized")
    df = replaceSubstring_Global(df, "LocationThreat", "Threatroom")
    df = replaceSubstring_Global(df, "cordinate", "coordinate")
    df = replaceSubstring_Global(df, "CapabilitiesRole",
            "Collaborationcollaborate")
    df = replaceSubstring_Global(df, "Knowledge", "Information")
    df = replaceSubstring_Global(df, "clarifyInformation", "clarify")
    df = replaceSubstring_Global(df, "askInformationLocation", 'askLocation')
#    df = replaceSubstring_Global(df, "Stabilized", "Victim") # see notes above
    df = replaceSubstring_Global(df, "Collaborationcollaborate",
            "Collaboration")
    df = replaceSubstring_Global(df, "wakeCritical", "collaborateCriticalWake")
    return df


def contingency_tables(df, colA, colB):
    """
    Purpose:
        Uses a Pandas package to create a continency table.

    Args:
        colA: Feature #1
        colB: Feature #2

    Returns: none
    """
    df_table = pandas.crosstab(index=df[colA],
            columns=df[colB], margins = True)


def investigate_replacedTerms(orig, colA, colB):
    """
    Purpose:
        Compare and contrast probabilities of features, given another features,
        before and after global replacement of labels. This function is useful
        for two reasons:
            1. to justify or reject concept-label granularity (as
               defined by strict adherence to Grounded Theory Qualitative
               Methodology)
            2. Domain definition in future work may include the knowledge
               engineering needs for certain words rejected or not used in
               this current domain (Study 3, ASIST).

    Args:
        orig: Original dataframe before replacement of substrings
        repl: Dataframe that contains replaced substrings.
        colA: First feature of interest. Conditioning feature.
        colB: Second feature of interest.

    Returns: None
    """
    ### Set some display options
    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 10)
    pandas.set_option('display.colheader_justify', 'center')

    ### Uncomment to display data description:
    #print(hrule, "Describe Numerical Data:\n", data.describe(), hrule)
    #print(hrule, "Describe Categorial Data:\n", data.describe(include=object), hrule)

    ### Make copy of categorical data to investigate:
    cat_orig = orig[["htns", "abstractLabels", "abstractLabels_v", "abstractLabels_nm", "causeLabels",
                    "questionLabels", "questionLabels_v", "questionLabels_nm",
                    "effectLabels", "qWord", "qPhrase", "auxVerb", "actionVerb"]]

    ### Current subset of interest:
    print(hrule, "Investigate original dataframe.\n\n")
    cat_orig= cat_orig[[colA, colB]]
    joint_cat_orig, common_joint_cat_orig = get_joint_probability(cat_orig, colA)
    cond_AB_cat_orig = get_conditional_probability(cat_orig, colA, colB)
    cond_BA_cat_orig = get_conditional_probability(cat_orig, colB, colA)


    ### Obtain count of joint probabilities, regardless of feature values
    count_joint_cat_orig = joint_cat_orig.groupby('joint_probability').size().to_frame()
    count_joint_cat_orig.reset_index(inplace = True)
    count_joint_cat_orig.columns = ["prob", "count"]
    print("Count of joint probabilities, regardless of feature values.\n\n", count_joint_cat_orig)
    print(count_joint_cat_orig.shape)

    ### See how the data change label objects are less granular:
    print(hrule, "Investigate same dataframe with replaced terms.\n\n")
    rData = replaceTerms(cat_orig)
    joint_rData, common_joint_rData = get_joint_probability(rData, 'questionLabels')
    count_joint_rData = joint_rData.groupby('joint_probability').size().to_frame()
    count_joint_rData.reset_index(inplace = True)
    count_joint_rData.columns = ['newProb', 'newCount']
    print("Count of joint probabilities of replaced labels, regardless of feature values.\n\n", count_joint_rData)

    ### For the question Labels for uncombined, granular labels
    sparse = joint_cat_orig[joint_cat_orig.joint_probability <= 0.01]
    print(hrule, "Sparse Question Labels: Granular\n\n", sparse.head())

    ### For the question Labels for combined, less granular labels
    r_sparse = joint_rData[joint_rData.joint_probability <= 0.01]
    print(hrule, "Sparse Question Labels: Combined\n\n", r_sparse.head())


def investigate_subset(df, colA='qPhrase', colB='abstractLabels',
        token_name='canYou'):
    """
    Purpose:
        This function investigates conditional probabilities of features,
        conditioned on either two other features or uttered text. The option to
        use uttered text is not currently supported in this file since it would
        require the uploading of HSR data. Until this data are made available
        to the public, the uttered text concept is replaced with an annotated
        key phrase.

    Args:
        df: Dataframe
        colA: First feature of interest; default feature: question phrases
        colB: Second feature of interset; default feature = abstract labels,
            which show intention of player.
        token_name: a string or substring defined by user; default substring is
            part of a common question utterance, "can you..."

    Returns: none
    """

    df = df[['obsNum', 'score', 'StartSeconds',
            'abstractLabels', 'questionLabels', 'qPhrase', 'actionVerb']]

    # Filter for all rows that mention the word 'which' in qPhrase
    token = df[colA].str.contains(token_name, case=False)

    # Now add this 'room' row back into the original dataframe, Not doing this
    # next step returns a [n x 2] dataframe of booleans. Don't forget this
    # step.
    token = df[token]
    print(hrule, "Rows with \'", token_name, "\' in qPhrase\n\n", token)

    ### Find joint and conditional probabilities of these subdatasets
    ###
    print("Joint probability of subset where \'", token_name, "\' is spoken\n\n")
    joint_token = get_joint_probability(token, 'questionLabels')
    print("Conditional probability of subset where \'", token_name, "\' is spoken\n\n")
    cond_token = get_conditional_probability(token, 'questionLabels', 'qPhrase')

    tokenCritical = token['questionLabels'].str.contains('critical', case = False)
    tokenCritical = token[tokenCritical]
    print(tokenCritical)

    print("Notice patterns when \'which\' is spoken", hrule)
    print("Describe Full DataFrame Categorial Data:\n", df.describe(include=object), hrule)
    print("Describe \'", token_name, "\' Categorial Data:\n", token.describe(include=object), hrule)
    print("Describe \'", token_name, "\' + critical Categorial Data:\n", tokenCritical.describe(include=object), hrule)


###############################################################################
##### PROGRAM STARTS HERE
###############################################################################

def main(file):
    """
    Purpose:
        Reads in dataset, cleans data, replaces terms, recleans data (if
        desired) and saves dataset with replaced terms

    Args:
        file: Relative path of data file to be used

    Returns:
        rdata: Cleaned and relabeled dataframe
    """

    ### Start Cleaning Process
    data = ctd.main(file)

    ### Replace granularity, save as a new csv file
    rdata = replaceTerms(data)

    ### Now clean this data again
    reclean(rdata, "abstractLabels", "abstractLabels")
    reclean(rdata, "causeLabels", "causeLabels")
    reclean(rdata, "questionLabels", "questionLabels")
    reclean(rdata, "effectLabels", "effectLabels")
    return data, rdata

###############################################################################
#   Program Starts Here
###############################################################################

if __name__ == '__main__':

    ### Read in the raw data
    file = "../data/commitOKAY_HSR-Removed_raw.csv"
    ### Send file to main() to be processed
    dataframe, r_dataframe = main(file)
    # Save the replaced Labels in a new csv file
    r_dataframe = pandas.DataFrame(r_dataframe)
    rFile = "../data/data_noHSR_replacedTerms_readyToUse.csv"
    r_dataframe.to_csv(rFile)

    if ORIGINAL_DATAFRAME:
        investigate_replacedTerms(dataframe, 'questionLabels', 'qPhrase')
        investigate_subset(dataframe, 'qPhrase')

    if REPLACED_DATAFRAME:
        investigate_replacedTerms(r_dataframe, 'questionLabels', 'qPhrase')
        investigate_subset(r_dataframe, 'qPhrase')

###############################################################################
#   Program Ends Here
###############################################################################
