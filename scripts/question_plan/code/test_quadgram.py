# Salena: Based on tutorial from https://medium.com/swlh/language-modelling-with-nltk-20eac7e70853

import nltk, re, pprint, string
import pandas
from nltk import word_tokenize, sent_tokenize

# For ease in reading terminal output
hrule = ("\n" + "-"*72 + "\n")

# Import and clean data:
string.punctuation = string.punctuation +'“'+'”'+'-'+'’'+'‘'+'—'
string.punctuation = string.punctuation.replace('.', '')
data = "../data/HDDL_dataset.csv"
data = pandas.read_csv(data)
data = pandas.DataFrame(data)
file = data["question_verbatim"]

for f in file:
    print(f)

# preprocess data
file_nl_removed = ""

for line in file:
    line_nl_removed = line.replace("\n", " ")      #removes newlines
    file_nl_removed += line_nl_removed
    file_p = "".join([char for char in file_nl_removed if char not in string.punctuation]) 

sents = nltk.sent_tokenize(file_p)
print("The number of sentences is", len(sents))

words = nltk.word_tokenize(file_p)
print("The number of tokens is", len(words))

average_tokens = round(len(words)/len(sents))
print("The average number of tokens per sentence is",average_tokens)

unique_tokens = set(words)
print("The number of unique tokens are", len(unique_tokens))



from nltk.util import ngrams
from nltk.corpus import stopwords
nltk.download('stopwords')

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


count = 4
print(hrule*2, "KEEPING STOP WORDS")
print_ngram_freq(freq_bigram, 2, count)
print_ngram_freq(freq_trigram, 3, count)
print_ngram_freq(freq_fourgram, 4, count)

print(hrule*2, "REMOVING STOP WORDS")
print_ngram_freq(freq_biX, 2, count)
print_ngram_freq(freq_triX, 3, count)
print_ngram_freq(freq_fourX, 4, count)



# TODO: Look into zero probability for natural language when
    # teams talk about plans, actions, or questions

# Add-1 smoothing is performed here.
# Salena: Based on tutorial from https://medium.com/swlh/language-modelling-with-nltk-20eac7e70853
ngrams_all = {1:[], 2:[], 3:[], 4:[]}

# Return back to original tokenized text
for i in range(4):
    for each in tokenized_text:
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
        ngram[-1] = round(temp, 4)

        #Prints top 10 unigram, bigram, trigram, fourgram after smoothing
print("Most common n-grams without stopword removal and with add-1 smoothing: \n")
for i in range(4):
    ngrams_prob[i+1] = sorted(ngrams_prob[i+1], key = lambda x:x[1], reverse = True)

# Salena todo
for i in range(1,5):
    print(hrule, "Most common", i, "-grams: \n")
    test = list(ngrams_prob[i][:10])
    for t in test:
        print(t)


