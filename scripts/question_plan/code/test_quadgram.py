# Salena: Based on tutorial from https://medium.com/swlh/language-modelling-with-nltk-20eac7e70853
"""
Note to self:
    file can be defined as either questionLabels or question_verbatim. just
    uncomment whichever I want.

    turn into list, then string for the code to clean properly

    questionLabels doesn't workw ith preprocessing that is in forloop soI just
    wrote my own with re.sub()

    sents should be defined as either file_p, the preprocessed file for
    question verbatim, or it should be defined as file_s, which is my version
    of a file string for questionLabels.


TODO:
    Do an argparse. 

    if arg == questionlabels:
        file = data[questionlabels]
        file_s = salena_process(file)
        sents = nltk.sent_tokenize(file_s)

    elif arg == abstractlabels:
        repeat for questionlables

    else: # assume question_verbatim
        file = data[question_verbatim]
        # Then use file_p, not file_s
        sents = nltk.sent_tokenize(file_p)

"""

import nltk, re, pprint, string
import pandas
from nltk import word_tokenize, sent_tokenize
from nltk.util import ngrams
from nltk.corpus import stopwords
nltk.download('stopwords')

import probability, cleanTheData

# For ease in reading terminal output
hrule = ("\n" + "-"*72 + "\n")

def salena_process(my_stuff):
    t1 = str(my_stuff)
    t1 = re.sub("\'", "", t1)
    t1 = re.sub(":", "", t1)
    t1 = re.sub("\"", "", t1)
    t1 = re.sub("\,", "", t1)
    t1 = re.sub("\?", "", t1)
    return t1




# Import and clean data:
string.punctuation = string.punctuation +'“'+'”'+'-'+'’'+'‘'+'—'
string.punctuation = string.punctuation.replace('.', '')
raw_data = "../data/final_raw_dataset.csv"
raw_data = pandas.read_csv(raw_data)
dataframe_0 = pandas.DataFrame(raw_data)

################################################################################
def less_granularity(df):
    """
    Purpose:
        Remove granularity from dataframe.
    """
    replace = input("Less granularity in labels?\ny - yes\n")
    if replace == "y":
        df = probability.replaceTerms(df)
    return df

################################################################################

dataframe = less_granularity(dataframe_0)

### Reclean Labels
probability.reclean(dataframe, "abstractLabels", "abstractLabels")
probability.reclean(dataframe, "questionLabels", "questionLabels")

ask = input("\na - abstractLabels\nl - questionLabels\nv - question_verbatim\n")
if ask == "v":
    file = dataframe["question_verbatim"]

    # preprocess data
    file_nl_removed = ""

    for line in file:
        line_nl_removed = line.replace("\n", " ")      #removes newlines
        file_nl_removed += line_nl_removed
        file_p = "".join([char for char in file_nl_removed if char not in string.punctuation]) 

elif ask == "a":
    file = dataframe["abstractLabels"]
    file = list(file)
    file_p = salena_process(file)

else:
    file = dataframe["questionLabels"]
    file = list(file)
    file_p = salena_process(file)

sents = nltk.sent_tokenize(file_p)
print("The number of sentences is", len(sents))

words = nltk.word_tokenize(file_p)
print("The number of tokens is", len(words))

average_tokens = round(len(words)/len(sents))
print("The average number of tokens per sentence is",average_tokens)

unique_tokens = set(words)
print("The number of unique tokens are", len(unique_tokens), hrule)



# No need for unigrams or stopwords, but I'll keep this part of the code since
# it comes with the tutorial (for now). --Salena
stop_words = set(stopwords.words('english'))
unigram=[]
bigram=[]
trigram=[]
fourgram=[]
tokenized_text = []

for sentence in sents:
    sentence = sentence.lower()
    sequence = word_tokenize(sentence)
    for word in sequence:
        if (word =='.'):
            sequence.remove(word)
        else:
            unigram.append(word)
    tokenized_text.append(sequence)
    bigram.extend(list(ngrams(sequence, 2)))
#unigram, bigram, trigram, and fourgram models are created
    trigram.extend(list(ngrams(sequence, 3)))
    fourgram.extend(list(ngrams(sequence, 4)))

# Count ngrams without stopword removal (Salena)
freq_bigram = nltk.FreqDist(bigram)
freq_trigram = nltk.FreqDist(trigram)
freq_fourgram = nltk.FreqDist(fourgram)



def removal(x):
# CONSIDER NOT USING THIS FUNCTION WHEN LOOKING AT LOGICAL ARGUMENTS
    # since these connectors give insight for planning and inference--Salena

# removes ngrams containing only stopwords
    y = []
    for pair in x:
        count = 0
        for word in pair:
            if word in stop_words:
                count = count or 0
            else:
                count = count or 1
        if (count==1):
            y.append(pair)
    return(y)

# Get stopwords removed
bigramX = removal(bigram)
trigramX = removal(trigram)
fourgramX = removal(fourgram)
freq_biX = nltk.FreqDist(bigramX)
freq_triX = nltk.FreqDist(trigramX)
freq_fourX = nltk.FreqDist(fourgramX)


def print_ngram_freq(freq, x=3, n=3):
    # Written by Salena
    # For easier reading of output
    freq_list = list(freq.most_common(n))
    print(hrule, "Most common", x, "grams: \n")
    for f in freq_list:
        print(f)


count = 6
print(hrule*2, "KEEPING STOP WORDS (No smoothing)")
print_ngram_freq(freq_bigram, 2, count)
print_ngram_freq(freq_trigram, 3, count)
print_ngram_freq(freq_fourgram, 4, count)

print(hrule*2, "REMOVING STOP (No smoothing) WORDS")
print_ngram_freq(freq_biX, 2, count)
print_ngram_freq(freq_triX, 3, count)
print_ngram_freq(freq_fourX, 4, count)


################################################################################
def smoothing(my_tokenized_text):
    # TODO: Look into zero probability for natural language when
        # teams talk about plans, actions, or questions

    # Add-1 smoothing is performed here.
    # Salena: Based on tutorial from https://medium.com/swlh/language-modelling-with-nltk-20eac7e70853
    ngrams_all = {1:[], 2:[], 3:[], 4:[]}

    # Return back to original tokenized text
    for i in range(4):
        for each in my_tokenized_text:
            for j in ngrams(each, i+1):
                ngrams_all[i+1].append(j);
    ngrams_voc = {1:set([]), 2:set([]), 3:set([]), 4:set([])}

    for i in range(4):
        for gram in ngrams_all[i+1]:
            if gram not in ngrams_voc[i+1]:
                ngrams_voc[i+1].add(gram)

    total_ngrams = {1:-1, 2:-1, 3:-1, 4:-1}
    total_voc = {1:-1, 2:-1, 3:-1, 4:-1}

    for i in range(4):
        total_ngrams[i+1] = len(ngrams_all[i+1])
        total_voc[i+1] = len(ngrams_voc[i+1])

    ngrams_prob = {1:[], 2:[], 3:[], 4:[]}

    for i in range(4):
        for ngram in ngrams_voc[i+1]:
            tlist = [ngram]
            tlist.append(ngrams_all[i+1].count(ngram))
            ngrams_prob[i+1].append(tlist)

    for i in range(4):
        for ngram in ngrams_prob[i+1]:
            # Add the +1 Smoothing:
            temp = (ngram[-1]+1)/(total_ngrams[i+1]+total_voc[i+1])

            # Round for ease of reading:
            ngram[-1] = round(temp, 2)

    for i in range(4):
        ngrams_prob[i+1] = sorted(ngrams_prob[i+1], key = lambda x:x[1], reverse = True)

    # Salena todo
    for i in range(1,5):
        print(hrule, "Most common", i, "sequence WITH smoothing: \n")
        test = list(ngrams_prob[i][:10])
        for t in test:
            print(t)

smoothing(tokenized_text)

################################################################################

"""
##### MODEL PREDICTION TODO: needs work

# From https://medium.com/swlh/language-modelling-with-nltk-20eac7e70853

str1 = 'what room should we'
str2 = 'first we should find all the criticals then collect them'

#smoothed models without stopwords removed are used
token_1 = word_tokenize(str1)
token_2 = word_tokenize(str2)
ngram_1 = {1:[], 2:[], 3:[]}   #to store the n-grams formed
ngram_2 = {1:[], 2:[], 3:[]}
for i in range(3):
    ngram_1[i+1] = list(ngrams(token_1, i+1))[-1]
    ngram_2[i+1] = list(ngrams(token_2, i+1))[-1]
print(hrule, "String 1: ", ngram_1,"\nString 2: ",ngram_2)

# Now we use the n-grams of the strings to get the next word predictions based on the highest probabilities.
for i in range(4):
    ngrams_prob[i+1] = sorted(ngrams_prob[i+1], key = lambda x:x[1], reverse = True)

pred_1 = {1:[], 2:[], 3:[]}
for i in range(3):
    count = 0
    for each in ngrams_prob[i+2]:
        if each[0][:-1] == ngram_1[i+1]:
#to find predictions based on highest probability of n-grams  

            count +=1
            pred_1[i+1].append(each[0][-1])
            if count ==5:
                break
    if count<5:
        while(count!=5):
            pred_1[i+1].append("NOT FOUND")
#if no word prediction is found, replace with NOT FOUND
            count +=1
for i in range(4):
    ngrams_prob[i+1] = sorted(ngrams_prob[i+1], key = lambda x:x[1], reverse = True)

pred_2 = {1:[], 2:[], 3:[]}

for i in range(3):
    count = 0
    for each in ngrams_prob[i+2]:
        if each[0][:-1] == ngram_2[i+1]:
            count +=1
            pred_2[i+1].append(each[0][-1])
            if count ==5:
                break
    if count<5:
        while(count!=5):
            pred_2[i+1].append("\0")
            count +=1


# Now we can call the above method for each n-gram to get the next word predictions according to each model.
print("Next word predictions for the strings using the probability models of bigrams, trigrams, and fourgrams\n")
print("Bigram model predictions: {}\nTrigram model predictions: {}\nFourgram model predictions: {}\n" .format(pred_1[1], pred_1[2], pred_1[3]))
print("Bigram model predictions: {}\nTrigram model predictions: {}\nFourgram model predictions: {}" .format(pred_2[1], pred_2[2], pred_2[3]))

"""

################################################################################


def investigate_subset(df, col= "abstractLabels", token_name = "critical"):
    """
    Purpose:
        To investigate subsets of dataframe, given an action or player
        intention.

    Args:
        df: dataframe before cleaning or processing, but after optional
            replacement of granular terms.
        colA: feature of interest (abstractLabels or questionLabels)
            Default column set to abstractLabels (player intention)
        token_name: substring of interest within column. Default
            interest is set to critical victims.

    Returns: none
    """
    # Set some display options for entire subset
    pandas.set_option('display.max_rows', 400)
    pandas.set_option('display.float_format', '{:.2}'.format)
    pandas.set_option('display.max_columns', 10)
    pandas.set_option('display.colheader_justify', 'center')

    df1 = df[["abstractLabels", "questionLabels", "question_verbatim"]]
    df2= df1[col].str.contains(token_name, case=False)
    df2 = df1[df2] # Ensure new dataframe
    print(hrule, df2.groupby("questionLabels").value_counts())



investigate_subset(dataframe, "abstractLabels", "collaborateCriticalWake")

# Do not put token_name as collaborateCarryVictim or *Stabilized. This will
    #yield false results if less granular or not!
investigate_subset(dataframe, "abstractLabels", "collaborateCarry")



