'''
--------------------------------------------------------------------------
This code will not run from the tomcat-planrec repo until I upload the csv data.
--------------------------------------------------------------------------

Author: Salena T. Ashton
        PhD Student, School of Information
        University of Arizona

Date Created: 5 July 2022
Last Updated: 5 July 2022

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


'''
I personalized the tutorial found at

https://www.analyticsvidhya.com/blog/2021/08/a-friendly-guide-to-nlp-bag-of-words-with-python-example/

for the purposes of this file.
'''
def bagOfWords(df):

    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 200)
    pandas.set_option('display.colheader_justify', 'center')
    pandas.set_option('display.width', 200)

########### Bag of Words From Scratch:
    utter = df['question_verbatim']
    print(type(utter))

    ### for scratch, Turn dataframe into a list
    utter = list(utter)


    ### For now, shorten the list:
    docs1= utter[0:19]
    docs2= utter[20:39]
    docs3= utter[40:59]
    docs4 = utter[60:79]
    for u in utter:
        print(u)


    ### Create wordset. Start with a list, then use the union1d. Turning it
        #  straight into a set will not work right.

    wordset = []

    ### Remove punctuations
    for i in utter:
        #print(i)
        j = re.sub(r"[^a-zA-Z0-9]", " ", i.lower()).split()
        #print(j, "\n")
        wordset = numpy.union1d(wordset, j)

    print(wordset)

    ### Define the function to extract the features in each document:
    def calc_bagOfWords(wordSet, doc):
        '''
        define dictionary with specified keys, which corresponds to the words
        of the vocabulary and specified value is 0.
        '''
        print("\n\tdoc = ", doc, "\n")
        tf_diz = dict.fromkeys(wordSet, 0)
        for word in doc:
            tf_diz[word] = doc.count(word)

        return tf_diz

    bow1 = calc_bagOfWords(wordset, utter[0])
    bow2 = calc_bagOfWords(wordset, utter[1])
    bow3 = calc_bagOfWords(wordset, utter[2])
    bow4 = calc_bagOfWords(wordset, utter[3])
    bow5 = calc_bagOfWords(wordset, utter[4])
    df_bow = pandas.DataFrame([bow1, bow2, bow3, bow4, bow5])
    print(Hrule, "df_bow.head()", df_bow.head())


########### Bag of Words Using Scikit_Learn
    pandas.set_option('display.max_columns', 200)
    from sklearn.feature_extraction.text import CountVectorizer
    from sklearn.feature_extraction import text
    print(Hrule, "\n\n from sklearn package:\n\n")

    # be sure to remove stop words
    ### customize stopwords
    # add list of specific room numbers
    salena_stop_words = text.ENGLISH_STOP_WORDS.union(['a3', 'b3', 'b8', 'c3', 'c6', 'c8', 'd2', 'd3', 'f4', 'g3', 'h1', 'h2', 'i2', 'i4', 'j1', 'j4', 'm1', 'm2'])
    vectorizer = CountVectorizer(stop_words = salena_stop_words)
    # In orer to slice lists for use, turn them to strings first:
    docs1 = str(docs1)
    docs2 = str(docs2)
    docs3 = str(docs3)
    docs4 = str(docs4)
    #vectorizer = CountVectorizer(stop_words = 'english', ngram_range=(2, 2))

    X = vectorizer.fit_transform([docs1, docs2, docs3, docs4])
    df_bow_sklearn = pandas.DataFrame(X.toarray(),columns=vectorizer.get_feature_names_out())
    print(df_bow_sklearn.head())


###############################################################################





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



bagOfWords(data)

print(Hrule, "\t\t\tEnd of Program", Hrule)

###############################################################################

