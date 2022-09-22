
#TODO: This file is still in development (8 September 2022)
"""
--------------------------------------------------------------------------
Purpose:
    Connect natural language to action prediction for plan recogition algorithm.

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Created:
    8 September 2022

Last Updated:
    8 September 2022

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

--------------------------------------------------------------------------
"""
import argparse
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
ORIGINAL_DATAFRAME = False
REPLACED_DATAFRAME = True ### Replaced labels from probability.py

### Horizontal ruling for visual ease in reading output.
hrule = ("\n" + "-"*80 + "\n")
Hrule = ("\n" + "="*80 + "\n")
#--------------------------------------------------------------------------


"""

    ### Customize stopwords: add list of specific room numbers
    salena_stop_words = text.ENGLISH_STOP_WORDS.union(['a1', 'a2', 'a3','a4',
        'a5', 'b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7', 'b8',
        'c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'c7', 'c8',
        'd1', 'd2', 'd3', 'e5', 'f4', 'g3', 'h1', 'h2', 'i2', 'i4', 'j1', 'j4',
        'm1', 'm2', 'm3', 'l1', 'k2', 'hey', 'just', 'did', '10', '11', '12',
        '13', '14', '15', '16', '17', '18', '19', '20', '21', '22', '23', '24',
        '25', '26', '27', '28', '29', '30', '31', '32', '33', '34', '35', '36',
        '37', '38', '39', '40', '41', '42', '43', '44', '45', '46', '47', '48'])
"""



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
    teamUtter1, teamUtter2, teamUtter3 = bagOfWords(df, "question_verbatim")

    ## Now send entire dataset, or team data subset, to find:
        # conditional probability of intention, given the utterance
        # conditional probabiity of utterance, given the player intent 
        # bagOfWords() called from within utterance_intent()

    list_intent = list(df["abstractLabels"].sort_values().unique())


    for i in list_intent:
        print(Hrule, "Player Intention:", i, "\n Word uttered:", utterance)
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
def get_trigram(data):
    import nltk
    import re
    nltk.download('punkt')

    #file = "just_638.csv"
    file = "doNotCommit3_HSR_replacedTerms_readyToUse.csv"
    data = pandas.read_csv(file)
    data = pandas.DataFrame(data)


    t1 = list(data['question_verbatim'])
    t1 = str(t1)
    t1 = re.sub("\'", "", t1)
    t1 = re.sub(":", "", t1)
    t1 = re.sub("\"", "", t1)
    t1 = re.sub("\,", "", t1)
    t1 = re.sub("\?", "", t1)
    tokens = nltk.word_tokenize(t1)
    trigrams = nltk.trigrams(tokens)
    bigrams = nltk.bigrams(tokens)


    print("\n\n\n Interactive, for now, for developing\n\n")
    answer = input("\n\tb - bigram or t - trigram \t?")
    if answer == "b":
        print("\n\nBigram Frequency Distribution:\n")
        ffreq_2 = nltk.FreqDist(bigrams)
        freq = dict(ffreq_2)

        # Subset by frequency > 2
        freq_2 = {key:value for key, value in freq.items() if value > 3}

        for w in sorted(freq_2, key=freq_2.get):
            print(w, freq_2[w])

        return freq_2

    else:
        print("\n\nTrigram Frequency Distribution:\n")
        ffreq_3 = nltk.FreqDist(trigrams)
        freq = dict(ffreq_3)

        # Subset by frequency > 2
        freq_3 = {key:value for key, value in freq.items() if value > 2}

        for w in sorted(freq_3, key=freq_3.get):
            print(w, freq_3[w])

        return freq_3


###############################################################################
def nl_conn(unsorted_df):
    """
    Purpose:

    Args:

    Returns:
    """

    mydf = unsorted_df[['question_verbatim', 'abstractLabels', 'questionLabels']]

    # DONE            1. Import replaced data frame 
    # DONE            2. Subset them by trigram
    # DONE NECESSARY? 3. Find probabilities of action, given trigram
    # DONE necessary? 4. Find probabilities of intention, given trigram
    # TODO            5. Markov model of plan recognition and action prediction
    # TODO            6. Write HDDL tasks and actions based off of this model

    trigram = {}
    trigram = get_trigram(trigram)

    for w in sorted(trigram, key=trigram.get):
            print(w, trigram[w])

    # Convert trigram dictionary back to a dataframe
    #df = pandas.DataFrame({"utterance": trigram.keys(), "utt_count": trigram.values()})

    def get_subset(utterance, mydf):
        subdf = mydf['question_verbatim'].str.contains(utterance, case=False, na = False)
        subdf = mydf[subdf]
        return subdf

    pandas.set_option('display.colheader_justify', 'right')

    for k in trigram.keys():
        k = ' '.join(k)
        print("Bigram or Trigram of Interest: ", k, "\n")
        my_subdf = get_subset(k, mydf)
        my_subdf = my_subdf.sort_values(by='abstractLabels')
        print(my_subdf, hrule)
        #print("FROM k in trigrams.keys()\n\n", my_subdf, hrule)




###############################################################################
def no_conn(unsorted_df, theUtterance, theIntent):

    unsorted_df = unsorted_df[['video', 'obsNum', 'regular', 'critical', 'score',
        'question_verbatim', 'abstractLabels', 'questionLabels']]
    df = unsorted_df.sort_values(by=['video'])



    ### Case = False for upper and lower case substrings
    ### na and nans are ignored when na = False
    utter = df['question_verbatim'].str.contains(theUtterance, case=False, na = False)
    utter = df[utter]
    intent = df['abstractLabels'].str.contains(theIntent, case = False, na=False)
    intent = df[intent]

#    print("Bag of Words for all utterances, given the word \'{}\' and given "
#            "the intent \'{}\'.".format(theUtterance, theIntent))
#    bagOfWords(intent, "question_verbatim")

    # The rest of this function is under construction:

    print(hrule, "Intent=", theIntent," | \"", theUtterance, "\" is spoken)")
    prob.get_joint_probability(utter, "abstractLabels")

    ### Given the label, what is the trigram probability?
    myLabel = input("Enter label of interest to find probability of trigram:\n")
    print("\nFor the question label:", myLabel, "Trigram probabilities are:\n")
    currentLabel = df['questionLabels'].str.contains(myLabel, case = False, na=False)
    cl = df[currentLabel]
    print(cl)
    print(len(cl))

###############################################################################
#   Program Starts Here
###############################################################################

parser = argparse.ArgumentParser()
parser.add_argument('--dataset', type=str, required = False)
parser.add_argument('--utterance', type=str, required = False)
parser.add_argument('--intent', type=str, required = False)
args = parser.parse_args()

"""

Use command line to specify word utterance of interest.

Example:
    For the uttered word, "want," enter this command:
    $ python bagOfWords.py --utterance want --dataset ../data/dataSet.csv

"""
print(args.utterance)
desired_word_utterance = args.utterance
myPath = args.dataset
myIntent = args.intent



if __name__ == '__main__':

#    if not args.utterance:
#        desired_word_utterance = "come"
#        print("\nDefault word utterance:", desired_word_utterance)
#        print("Enter word at command line, if desired.\n   Example: $ python bagOfWords.py --utterance want \n\n")
#        time.sleep(3)

    if ORIGINAL_DATAFRAME:
            ### Read in the data
        if args.dataset:
            data = pandas.read_csv(myPath)
            data = pandas.DataFrame(data)
            main(data, desired_word_utterance)
            print(hrule, "\tEnd of Original Dataset Process for the uttered word \'{}\'.".format(desired_word_utterance),  Hrule)

        else:
            file = "../data/HSR/doNotCommit2_HSR_readyForUse.csv"
            data = pandas.read_csv(file)
            data = pandas.DataFrame(data)
            main(data, desired_word_utterance)
            print(hrule, "\tEnd of Original Dataset Process for the uttered word \'{}\'.".format(desired_word_utterance),  Hrule)

    if REPLACED_DATAFRAME:
        if args.dataset:
            rdata = pandas.read_csv(myPath)
            rdata = pandas.DataFrame(rdata)

        else:
            relabeled_file = "doNotCommit3_HSR_replacedTerms_readyToUse.csv"
            rdata = pandas.read_csv(relabeled_file)
            rdata = pandas.DataFrame(rdata)

#        main(rdata, desired_word_utterance)
#        print(hrule, "\tEnd of Replaced-label Dataset Process for the uttered word \'{}\'.".format(desired_word_utterance),  Hrule)
        time.sleep(1)
        nl_conn(rdata)


        if args.intent:
            print("Intent, given the utterance")
            abstractLabel_subset(rdata, myIntent)

###############################################################################
#   Program Ends Here
###############################################################################
