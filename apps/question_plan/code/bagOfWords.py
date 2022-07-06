'''
--------------------------------------------------------------------------
This code will not run from the tomcat-planrec repo until I upload the csv data.
--------------------------------------------------------------------------

Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 5 July 2022
Last Updated: 6 July 2022

Dr. Adriana Picoral, Instructor INFO 692
School of Information, University of Arizona

Purpose: Intro to NLP Implementation, as encountered in Eisenstein book.

--------------------------------------------------------------------------


Sources used considerably:

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
import collections
import re
from nltk.stem import PorterStemmer
from nltk.tokenize import word_tokenize
from nltk.stem import WordNetLemmatizer
import nltk

nltk.download('punkt')
nltk.download('wordnet')
nltk.download('omw-1.4')
ps = PorterStemmer()
lemmatizer = WordNetLemmatizer()

import probability as prob
'''
I personalized and combined the tutorials found at:

    * https://www.analyticsvidhya.com/blog/2021/08/a-friendly-guide-to-nlp-bag-of-words-with-python-example/
    * https://www.machinelearningplus.co/np.lemmatization-examples-python/

for the purposes of this file.
'''


def bagOfWords(unsorted_df):
    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 200)
    pandas.set_option('display.colheader_justify', 'center')
    pandas.set_option('display.width', 200)

    '''
    Normally, we do not sort our data when analyzing but I will sort by video
    in order to compare different teams and different missions per team.
    '''
#    print(unsorted_df.head(10))
    unsorted_df = unsorted_df[['video', 'obsNum', 'regular', 'critical', 'score',
        'question_verbatim', 'abstractLabels', 'questionLabels']]
    df = unsorted_df.sort_values(by=['video'])
#    print(df.head(113))

    ### Divide up the dataframe by teams:
    team1 = (df['video'] == 633) | (df['video'] == 634)
    team1 = df[team1]
#    print(hrule, "Team1\n", team1)
#    print(team1.shape, type(team1))

    team2 = (df['video'] == 635) | (df['video'] == 636)
    team2 = df[team2]
#    print(hrule, "team2\n", team2)

    team3 = (df['video'] == 637) | (df['video'] == 638)
    team3 = df[team3]
#    print(hrule, "Team3\n", team3, Hrule)

    ### Divide up the dataframe by teams:
    def divideFrame(team):
        docs = team['question_verbatim'].to_frame()
        docs.reset_index(inplace = True)
        docs.drop(docs.columns[0], axis = 1, inplace = True)
#        print(hrule, docs.shape, type(docs))
#        print(docs.head(30))
        return docs


    docs1= divideFrame(team1)
    docs2= divideFrame(team2)
    docs3= divideFrame(team3)


########### Bag of Words Using Scikit_Learn
    pandas.set_option('display.max_columns', 600)
    from sklearn.feature_extraction.text import CountVectorizer
    from sklearn.feature_extraction import text
#    print(Hrule, "\n\n from sklearn package:\n\n")

    # be sure to remove stop words
    ### customize stopwords
    # add list of specific room numbers
    salena_stop_words = text.ENGLISH_STOP_WORDS.union(['a1', 'a2', 'a3','a4',
        'a5', 'b1', 'b2', 'b3', 'b4', 'b5', 'b6', 'b7', 'b8',
        'c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'c7', 'c8', 
        'd1', 'd2', 'd3', 'e5', 'f4', 'g3', 'h1', 'h2', 'i2', 'i4', 'j1', 'j4',
        'm1', 'm2', 'm3', 'l1', 'k2', 'hey', 'just', 'did', '10', '11', '12',
        '13', '14', '15', '16', '17', '18', '19', '20', 'english'])
    # In orer to slice lists for use, turn them to strings then lemmatize:


    def stringLemma(doc):
        doc = str(doc)
        docWords = nltk.word_tokenize(doc)
        docLem = ' '.join([lemmatizer.lemmatize(w) for w in docWords])
        return docLem


    doc1 = stringLemma(docs1)
    doc2 = stringLemma(docs2)
    doc3 = stringLemma(docs3)

    ### First vectorize 1 by 1
    print(hrule, "For 1 by 1 ngram\n\n")
    vectorizer = CountVectorizer(stop_words = salena_stop_words, ngram_range=(1,1))
    X = vectorizer.fit_transform([doc1, doc2, doc3])
    df_bow_sklearn = pandas.DataFrame(X.toarray(),columns=vectorizer.get_feature_names_out())
    print(df_bow_sklearn.head(200))

    '''
    ### Then vectorize 2 by 2
    print(hrule, "For 2 by 2 ngram\n\n")
    vectorizer = CountVectorizer(stop_words = salena_stop_words, ngram_range=(2,2))
    X = vectorizer.fit_transform([doc1, doc2, doc3])
    df_bow_sklearn = pandas.DataFrame(X.toarray(),columns=vectorizer.get_feature_names_out())
    print(df_bow_sklearn.head(200))
    '''

    print("End of bagOfWords()")


###############################################################################
def abstractLabel_subset(df, theIntent):
    '''
    Separate df by abstaction labels to identify intentions and correlate them
    to possible verbatim clues.

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

    '''

    joint = prob.get_joint_probability(df, "abstractLabels")


    ### When the Team is concerned with a particular abstract level of
        # intention, we will subset that intention from the abstraction labels.

    myIntent = df['abstractLabels'].str.contains(theIntent, case = False)
    myIntent = df[myIntent]

    # Remove first column since importing the joint prob function adds it. 
    #TODO: fix this bug.
    myIntent.drop(myIntent.columns[0], axis=1, inplace=True)
    myIntent = myIntent.sort_values(by=['video'])
#    print(hrule, "All observations that have the word \"", theIntent,
#            "\" in abstract labels.\n\n", myIntent.head(191))
    return myIntent

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
### Read in the data
file = "../data/doNotCommit2_HSR_replacedTerms_readyToUse.csv"

print(hrule, "\t...reading in file...", file, "\n")
data = pandas.read_csv(file)
print(hrule, "\nChecking head(3) of myCleanedData:\n\n", data.head(3), hrule)


### Uncomment to send the entire dataset to bagOfWords
print(Hrule, "FOR ALL INTENTIONS\n")
bagOfWords(data)

### Send a specific player intention to the bagOfWords(). In this case, we will
    ### Investigate the intention to 'carry' a victim or potential victim.

    # First subset the dataset with all abstraction labels with the word of
      # interest for intentions, as captured in abstraction labels:
intent = "critical"
print(Hrule, "FOR THE INTENT:", intent, "\n")
carryIntention = abstractLabel_subset(data, intent)
    # Now send to the bagOfWords() function:
bagOfWords(carryIntention)


print(Hrule, "\t\t\tEnd of Program", Hrule)

###############################################################################
