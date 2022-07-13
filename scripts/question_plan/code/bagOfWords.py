#TODO: Start documentation on line 218.
"""
--------------------------------------------------------------------------
Purpose:
    This file uses bag of words and functions from probability.py for the
    preliminary analysis of linking word utterances and annotated data.

    This file depends on HSR data. Adjust your relative path at the end of this
    file to read in this data.

TODO:
    Argparse for user path to HSR data.

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Created:
    5 July 2022

Last Updated:
    13 July 2022

Affiliation:
    Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
    Adarsh Pyarelal, Head PI and Clayton T. Morrison, Co-PI
    School of Information, University of Arizona
--------------------------------------------------------------------------
File Dependencies:
    cleanTheData.py
    probability.py

Attributes of comments in file to be aware of:
    '###' Single-line comments for user.
    '#' Commands that can be uncommented. Most of these are either print
        statements for debugging or data exploration samples/ heads.

Functions in File:
    abstractLabel_subset(df, theIntent)
    bagOfWords(unsorted_df, column)
    divideFrame(team)
    stringLemma(doc)
    utterance_intent(unsorted_df, theUtterance, theIntent)
    main()

--------------------------------------------------------------------------
"""

import collections
import datetime
import matplotlib.pyplot as pyplot
import nltk
from nltk.stem import PorterStemmer
from nltk.tokenize import word_tokenize
from nltk.stem import WordNetLemmatizer
import numpy
import pandas
import requests
import re
import scipy.stats as stats
from sklearn import linear_model
import sys
import time

import probability as prob

nltk.download('punkt')
nltk.download('wordnet')
nltk.download('omw-1.4')
ps = PorterStemmer()
lemmatizer = WordNetLemmatizer()

#--------------------------------------------------------------------------
### Set to true or false to run program for each desired dataframe.
ORIGINAL_DATAFRAME = True
REPLACED_DATAFRAME = True ### Replaced labels from probability.py

### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*80 + "\n")
Hrule = ("\n" + "="*80 + "\n")
#--------------------------------------------------------------------------





def bagOfWords(unsorted_df, column = "question_verbatim"):
    """
    Purpose:
        The design of this function is still in progress.

        1. Word analysis for player utterances by:
            * The entire dataframe
            * Subset dataframes by teams or videos
        2. Customized stop-words that are domain-specific
        3. Minimal Lemmatization (requires some human analysis, by design)
        4. Uncomment to view ngram 1x1 or 2x2


    Args:
        unsorted_df: unsorted dataframe, which will later be sorted to filter
            by video or utterance.
        column: Feature of Interest. Default set as "question_verbatim".

    Output:
        Vectorized print of words by full dataframe or by team.

    Returns:
        team1, team2, ... teamN: subset dataframe by team.

    Resources used:
        1. https://www.analyticsvidhya.com/blog/2021/08/a-friendly-guide-to-nlp-bag-of-words-with-python-example/
        2. https://www.machinelearningplus.co/np.lemmatization-examples-python/
        3. Guidance from Dr. Adriana Picoral, assistant professor, School of
        Information, University of Arizona (Info 692 Directed Research, Summer
        2022)
    """

    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 200)
    pandas.set_option('display.colheader_justify', 'center')
    pandas.set_option('display.width', 200)

    ### Sort by video to compare different teams and different missions per team.
    unsorted_df = unsorted_df[['video', 'obsNum', 'regular', 'critical', 'score',
        'question_verbatim', 'abstractLabels', 'questionLabels']]
    df = unsorted_df.sort_values(by=['video'])
#    print(df.head(113))

    ### Divide up the dataframe by teams:
    #TODO: argparse for team binning
    team1 = (df['video'] == 633) | (df['video'] == 634)
    team1 = df[team1] ### Reset as a dataframe for all features
#    print(hrule, "Team1\n", team1)
#    print(team1.shape, type(team1))

    team2 = (df['video'] == 635) | (df['video'] == 636)
    team2 = df[team2]
#    print(hrule, "team2\n", team2)
#    print(team2.shape, type(team2))

    team3 = (df['video'] == 637) | (df['video'] == 638)
    team3 = df[team3]
#    print(hrule, "Team3\n", team3, hrule)
#    print(team3.shape, type(team3))

    def divideFrame(team):
        docs = team[column].to_frame()
        docs.reset_index(inplace = True)
        docs.drop(docs.columns[0], axis = 1, inplace = True)
#        print(hrule, docs.shape, type(docs))
#        print(docs.head(30))
        return docs

    ### Reset the dataframes' columns
    docs1= divideFrame(team1)
    docs2= divideFrame(team2)
    docs3= divideFrame(team3)

    ### Bag of Words Using Scikit_Learn
    pandas.set_option('display.max_columns', 600)
    from sklearn.feature_extraction.text import CountVectorizer
    from sklearn.feature_extraction import text

    ### Customize stopwords: add list of specific room numbers
    salena_stop_words = text.ENGLISH_STOP_WORDS.union(['a1', 'a2', 'a3','a4',
        'a5', 'b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7', 'b8',
        'c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'c7', 'c8',
        'd1', 'd2', 'd3', 'e5', 'f4', 'g3', 'h1', 'h2', 'i2', 'i4', 'j1', 'j4',
        'm1', 'm2', 'm3', 'l1', 'k2', 'hey', 'just', 'did', '10', '11', '12',
        '13', '14', '15', '16', '17', '18', '19', '20', 'english'])


    def stringLemma(doc):
        """
        Purpose:
            In order to slice lists for use, turn them to strings, then
            lemmatize. This function currently uses WordNetLemmatizer().

        Args:
            doc: Dataframe or subset dataframe of interest

        Returns:
            docLem: tokenized and lemmatized dataframe.
        """
        doc = str(doc)
        docWords = nltk.word_tokenize(doc)
        docLem = ' '.join([lemmatizer.lemmatize(w) for w in docWords])
        return docLem


    doc1 = stringLemma(docs1)
    doc2 = stringLemma(docs2)
    doc3 = stringLemma(docs3)

    ### First vectorize 1 by 1
    print(hrule, "For 1 by 1 ngram\nFirst Row = First Team, etc...\n")
    vectorizer = CountVectorizer(stop_words = salena_stop_words, ngram_range=(1,1))
    X = vectorizer.fit_transform([doc1, doc2, doc3])
    df_bow_sklearn = pandas.DataFrame(X.toarray(),columns=vectorizer.get_feature_names_out())
    print(df_bow_sklearn.head(200))

    """
    ### Then vectorize 2 by 2
    print(hrule, "For 2 by 2 ngram\n\n")
    vectorizer = CountVectorizer(stop_words = salena_stop_words, ngram_range=(2,2))
    X = vectorizer.fit_transform([doc1, doc2, doc3])
    df_bow_sklearn = pandas.DataFrame(X.toarray(),columns=vectorizer.get_feature_names_out())
    print(df_bow_sklearn.head(200))
    """

    return team1, team2, team3

###############################################################################
def utterance_intent(unsorted_df, theUtterance, theIntent):
    """
    Purpose:

    Args:

    Returns:
    """

    unsorted_df = unsorted_df[['video', 'obsNum', 'regular', 'critical', 'score',
        'question_verbatim', 'abstractLabels', 'questionLabels']]
    df = unsorted_df.sort_values(by=['video'])

    """
    Create two subset dataframes, one for all observations that have
    utterance of interest and the other for the intent of interest
    """
    utter = df['question_verbatim'].str.contains(theUtterance, case=False)
    utter = df[utter]
    intent = df['abstractLabels'].str.contains(theIntent, case = False)
    intent = df[intent]

    print(hrule, "Probabilities of ALL Intentions, given the utterance\"{}\" in the question.".format(theUtterance))
    prob.get_joint_probability(utter, "abstractLabels")

    print(hrule, "Bag of Words for ALL Utterances, given the intent:", theIntent)
    bagOfWords(intent, "question_verbatim")

    """
    # The rest of this function is under construction:

    print(hrule, "Intent=", theIntent," | \"", theUtterance, "\" is spoken)")
    prob.get_conditional_probability(utter, "question_verbatim", "abstractLabels")
    print("Ends here\n")

    # Now send to bag of words ()
    bagOfWords(utter, "abstractLabels")
    print("End of bagOfWords() for utterance:", theUtterance, "\n")

    ### Find the conditional probability of utterance, given itent:
    print(hrule, "\np(\"", theUtterance, "\" is spoken", " | Intent=", theIntent, ")\n")
    cond_intent = prob.get_conditional_probability(intent, "abstractLabels", "question_verbatim")
    print("Ends here\n")

    # now send to bag of word:
    print("End of bagOfWords() for the intent:", theIntent, "\n")
    """

###############################################################################


def abstractLabel_subset(df, theIntent):
    """

    This function is in progress.

    Purpose:
        Separate df by abstaction labels to identify intentions and correlate them
        to possible verbatim clues.

    Args:

    Returns:

        The following abstractions labels occur more than twice, or at a joint
        probability of > 0.1 and these will be the focus of the rest of this
        function for the present time.

                    ABSTRACT LABEL           JOINT PROBABILITY

                            askLocation        0.021

        collaborateCriticalThreatroom        0.016
            collaborateCriticalLocation        0.031
                collaborateCriticalWake         0.12
            collaborateCriticalPriority        0.021

            collaborateRescueTeammate        0.026
            collaborateLocationVictim        0.031
                collaborateCarryVictim         0.15
                collaborateClearLocation        0.037

                    coordinatePlanTeam        0.047
                    clearLocationVictim        0.058

                prioritizeCriticalVictim        0.016
                prioritizeClearLocation        0.021
            prioritizeCriticalLocation        0.063

                            rescueVictim        0.016
                shareInformationUnique        0.063

    """
    print("Joint Probabilities of all Abstract Labels:\n\n")
    joint = prob.get_joint_probability(df, "abstractLabels")


    ### When the Team is concerned with a particular abstract level of
        # intention, we will subset that intention from the abstraction labels.

    myIntent = df['abstractLabels'].str.contains(theIntent, case = False)
    myIntent = df[myIntent]
    print("Conditional Probabilities of Abstract Labels with Intent:", theIntent, "\n\n")
    Intent_joint = prob.get_joint_probability(myIntent, "abstractLabels")
    print("Conditional Probabilities of Question Labels with Intent:", theIntent, "\n\n")
    qIntent_joint = prob.get_joint_probability(myIntent, "questionLabels")


    # Remove first column since importing the joint prob function adds it. 
    #TODO: fix this bug.
    myIntent.drop(myIntent.columns[0], axis=1, inplace=True)
    myIntent = myIntent.sort_values(by=['video'])
    myIntent["0"] = range(1, 1+len(myIntent))
    print("All observations that have the word \"{}\" in abstract labels.".format(theIntent), myIntent.head(191))
    return myIntent


def get_intention_components(df, iList):
    """
    This function is in progress. As of 13 July, this function is implemented
    as an user-interactive loop to ease development and troubleshooting. The
    final implementation will not have this interaction.

    Purpose:
        To compare specific intention components with word utterances.

    Args:
    Returns:
    """

    ## This loop requires user interaction, which can be annoying to some.

    intentions = ['carry', 'wake', 'priorit', 'locat', 'unique', 'information',
    'plan', 'clear', 'critical', 'stabilize', 'ask', 'request', 'suggest']

    for i in intentions:
        carryIntention = abstractLabel_subset(data, i)
        print(hrule)
        ask = input("Hit c to continue to next\n")
        if ask == "c":
            continue
        else:
            break


def main(df, utterance):
    """
    Purpose:
        This main function splits dataframe into subsets by team, obtains bag
        of words, counts, and calculates the joint or conditional probability
        of a word or intention, conditioned on the other.

    Args:
        df: dataframe
        utterance: word of interest

    Returns: None
    """
    ### Send the entire dataset to bagOfWords, split into teams to compare and contrast.
    print("\n\nFOR ALL INTENTIONS AND UTTERANCES:")
    teamUtter1, teamUtter2, teamUtter3 = bagOfWords(df, "question_verbatim")
    print(teamUtter1)

    ## Now send entire dataset, or team data subset, to find:
        # conditional probability of intention, given the utterance
        # conditional probabiity of utterance, given the player intent 
        # bagOfWords() called from within utterance_intent()

    list_intent = list(df["abstractLabels"].sort_values().unique())

    for i in list_intent:
        print(hrule, "For Player Intention:", i, "\n Word uttered:", utterance)
        utterance_intent(df, utterance, i)

    print("Joint Probabilities of all Abstract Labels:\n\n")
    joint, joint_tail = prob.get_joint_probability(df, "abstractLabels")

    myJoint = joint.sort_values(by=['abstractLabels'])
    print(myJoint.head(200))

    """
    ### The rest of this program is still under construction

    print("\nFOR THE INTENT:", intent, "\n")
    subsetIntention = abstractLabel_subset(data, intent)
        # Now send to the bagOfWords() function:
    bagOfWords(subsetIntention, "question_verbatim")


    print("\nFOR THE UTTERANCE:", utterances, "\n")
    bagOfWords(subsetIntention, "question_verbatim")
    print("\nEnd of intent =", intent)

    """

###############################################################################
#   Program Starts Here
###############################################################################
"""
Set desired word utterance in line below to begin program.
"""
desired_word_utterance = "want"


if __name__ == '__main__':

    if ORIGINAL_DATAFRAME:
        ### Read in the data
        file = "../data/HSR/doNotCommit2_HSR_readyForUse.csv"
        data = pandas.read_csv(file)
        data = pandas.DataFrame(data)
        main(data, desired_word_utterance)
        print(hrule, "\tEnd of Original Dataset Process for the uttered word \'{}\'.".format(desired_word_utterance),  Hrule)

    if ORIGINAL_DATAFRAME & REPLACED_DATAFRAME:
        time.sleep(2)

    if REPLACED_DATAFRAME:
        relabeled_file = "../data/HSR/doNotCommit3_HSR_replacedTerms_readyToUse.csv"
        rdata = pandas.read_csv(relabeled_file)
        rdata = pandas.DataFrame(rdata)
        main(rdata, desired_word_utterance)
        print(hrule, "\tEnd of Replaced-label Dataset Process for the uttered word \'{}\'.".format(desired_word_utterance),  Hrule)

###############################################################################
#   Program Ends Here
###############################################################################
