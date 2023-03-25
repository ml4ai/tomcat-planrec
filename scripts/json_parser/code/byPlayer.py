"""
Note to self: same as other but by obs, then player to avoid Simpson's Paradox
--------------------------------------------------------------------------
Note to Charlie Gomez:
    plotnine does not allow multiple plots on one graph like ggplot. I tried
    the patchworklib package and several other methods of factorizing the data,
    but it will only work for one graph at a time.
--------------------------------------------------------------------------
Purpose:

    This file explores data collected by Salena Torres Ashton for the Theory
    of Mind-based Cognitive Architecture for Teams (ToMCAT), PI: Adarsh
    Pyarelal.

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Created:
    23 November 2022

Affiliation:
    Computational Social Science (Info 514)
    Dr. Charles J. Gomez, School of Sociology
    University of Arizona
--------------------------------------------------------------------------

Attributes of comments in file to be aware of:

--------------------------------------------------------------------------
"""
import argparse
import pandas
import matplotlib.pyplot as pyplot
import numpy
from plotnine import *
from dfply import *
import random
import nltk
from nltk.util import ngrams
import sys

# For ease in reading terminal output:
hrule = ("\n"+"-"*80+"\n")
Hrule = ("\n"+"-"*80)
hr = ("\n"+" -"*20+"\n")
br = ("\n\n")
pandas.set_option('display.max_rows', 500)
pandas.set_option('display.max_columns', 500)
pandas.set_option('display.width', 600)

# Helper Functions
def normalize_column(col):
    return (col/col.abs().max())

def joint(col):
    return(col/col.sum())

def delete_player_label(tokens):
    player = ["Red", "Blue", "Green"]
    new = [i for i in tokens if i not in player]
    return new

def plot_frequency(top, keyWord):
    print(hrule, "DataFrame to be plotted:\n", top, hrule)
    ashton_freq = (ggplot(top, aes(x = 'key' , y = 'value', fill='value')) +
    geom_bar(stat='identity') +
    scale_fill_gradient2(low = "darkorange", high = "blue",
                         mid = "steelblue", midpoint = 2500, guide=False) +
    scale_x_discrete(limits=top['key'].tolist(), trans = 'log2') +
    labs(title="Top 300 N-grams ") +
    xlab("Trigram" ) + ylab("Count") +
    theme_linedraw() +
    coord_flip() +
    theme(panel_grid=element_blank()))
    keyword = ("300_"+keyWord)
    ashton_freq.save(keyword)

def prep_for_cdf_plot(df, which):
    first = df[which]
    ffdist = nltk.FreqDist(first)
    which_df = pandas.DataFrame(ffdist.most_common(10), columns=('key',
        'value'))
    print("Which_DF:\n", which_df)
    return which_df


def plot_cdf(df, var = 'value', title='CDF of Entire N-Gram', color="black"):
    cdf = (ggplot(df, aes(x = var)) +
            stat_ecdf(geom= 'step', size=2, color=color) +
            xlim(0, 400)+
            labs(title=title, x="Token Frequency",y="Cumulative Fraction")+
    theme_linedraw())
    #print(cdf)
    filename = ("300_"+title)
    cdf.save(filename)
###############################################################################


def trigram(tokens, df):
    # Remove repeated tokens in any single potential n-gram we'll create
    new = []
    first = tokens[0]
    new.append(first)
    a = first
    for t in tokens:
        b = t
        if a == b:
            continue
        else:
            if a != "ProximityBlockInteraction":
                if b != "ProximityBlockInteraction":
                    new.append(a)
        a = b
    nice = pandas.Series(new)
    nnice = nltk.FreqDist(ngrams(nice, 3))
    return nnice


def bigram(tokens,df):
    # Remove repeated tokens in any single potential n-gram we'll create
    new = []
    first = tokens[0]
    new.append(first)
    a = first
    ask = input("\n Include dialogue events? y/n \n")
    for t in tokens:
        b = t
        if ask == "n":
            if a == b:
                continue
            else:
                # remove keep from this so I can remove proximity interaction
                   # from n-grams.
                if "keepInteraction" not in a:
                    if "keepInteraction" not in b:
                        if "Item" not in a:
                            if "Item" not in b:
                                if "dialogue" not in a:
                                    if "dialogue" not in b:
                                        new.append(a)
        else:
            if a == b:
                continue
            else:
                if "Interaction" not in a:
                    if "Interaction" not in b:
                        if "Item" not in a:
                            if "Item" not in b:
                                new.append(a)
        a = b
    nice = pandas.Series(new)
    nnice = nltk.FreqDist(ngrams(nice, 2)) 
    return nnice


def investigate_ngram(ng, n):
    """
    n = 2 or 3 for ngram
    """
    # First we investigate bigrams by frequency
    nice_d = pandas.DataFrame(ng.most_common(300), columns=("key", "value"))
    print("Number of rows total:", nice_d['value'].sum())
    nice_d['key'] = nice_d['key'].astype(str)
    nd = nice_d.replace('\(', '', regex = True)
    nd = nd.replace('\)', '', regex = True)
    nd['normalized'] = round(normalize_column(nd['value']), 3)
    nd['joint'] = round(joint(nd['value']), 3)
    #print(hrule, "Investigating", n, "N-Gram Frequencies\n", nd.head(300))

    # Then we investigate the conditional probabilities of tokens
    if n==2:
        plot_frequency(nice_d, "Bigram_Frequency")
        plot_cdf(nice_d, title="Bigram_Cumulative_Frequency")
        nd[['First', 'Second']] = nd['key'].apply(lambda x: pandas.Series(str(x).split(",")))
        print("ND:", nd)
        # Prep to plot cdf of first token, then last token:
        first = prep_for_cdf_plot(nd, 'First')
        plot_cdf(first, "value", "First_Token_CDF_of_Bigram", color="blue")
        second = prep_for_cdf_plot(nd, 'Second')
        plot_cdf(second, "value", "Second_Token_CDF_of_Bigram", "red")
        # prep for additional probability stats:
        cleaned = nd[['First', 'Second']]
    if n==3:
        plot_frequency(nice_d, "Trigram_Frequency")
        plot_cdf(nice_d, title="Trigram_Cumulative_Frequency")
        # Prep to plot cdf of first token, then last token:
        nd[['First', 'Second', 'Third']] = nd['key'].apply(lambda x: pandas.Series(str(x).split(",")))
        first = prep_for_cdf_plot(nd, 'First')
        plot_cdf(first, "value", "First_Token_CDF_of_Trigram", "blue")
        second = prep_for_cdf_plot(nd, 'Second')
        plot_cdf(second, "value", "Second_Token_CDF_of_Trigram", "red")
        third = prep_for_cdf_plot(nd, 'Third')
        plot_cdf(third, "value", "Third_Token_CDF_of_Trigram", "yellow")
        # prep for additional probability stats:
        cleaned = nd[['First', 'Second', 'Third']]

    done = cleaned.groupby('First').value_counts(normalize = True).to_frame()
    done.reset_index(inplace = True)
    done = done.rename(columns={0: 'cond_probability'})
    done['cond_probability'] = round(done['cond_probability'], 3)
    print(hrule, "Investigating", n, "N-Gram Conditional Probabilities\n")
    print(done.sort_values(by=['cond_probability'], ascending=False).head(100))
    #print("Number of rows:", len(cleaned.index))


def main(feature, df):
    """
    feature: dataframe feature of interst
    """
    main_tokens = df[feature]
    fdist = nltk.FreqDist(main_tokens)
    #print(hrule, "Most Common Terms:\n")
    commonTerms = fdist.most_common(100)
    for c in commonTerms:
        print(c)

    return main_tokens

def descriptive(dfAll):
    print(hrule*3, "Final number of possible n-gram tokens for each column:\n")
    print(dfAll.describe(include='all'), hr)
    df = dfAll[['obs', 'topic', 'player', 'subtype', 'rule', 'specific']]
    df['obs'] = df['obs'].astype(str)
    for d in df.columns:
        # use unique().size for counts of unique()
        print(hr, d, br, df[d].unique().size)
        action = pandas.Categorical(df[d])
        print("\n", hrule, "Descriptive Statistics of Categorical Data for", d, ":\n",
                action.describe().sort_values(by=['freqs'], ascending = False),
                hrule)

    # Subset by video observation and player
def byPlayer(df):
    df = df[['obs', 'timestamp', 'time_passed', 'player', 'subtype', 'specific']]
    grouped = df.groupby(['obs', 'player'])
    for o, p in grouped:
        print(Hrule*2)
        print(o)
        print(p)
        for d in df.columns:
            action = pandas.Categorical(df[d])
            print("\n", hrule, "Descriptive Statistics of Categorical Data for", d, ":\n",
                    action.describe().sort_values(by=['freqs'], ascending =
                        False).head(10), hrule)


#----------------------------------------------------------------------
parser = argparse.ArgumentParser()

### Possible args for column: descriptive, subtype, rule, specific. 
    ### Default feature: specific
parser.add_argument('--column', type = str, required = False)

### Possible args for set:
    # all: all observations and players in dataset
    # obs: subset by observation and player
parser.add_argument('--set', type = str, required = False)
args = parser.parse_args()
print(args.column, "is the chosen dataframe column of interest.\n")
my_feature = args.column
my_set = args.set

if __name__ == '__main__':
    df0 = pandas.read_csv("../data/total_631_700.csv")
    df1 = df0.replace('MarkerPlaced', 'Marker', regex=True)
    df1 = df1.replace('MarkerRemoved', 'Marker', regex=True)
    print("Final number of Rows:", len(df1.index))

    if args.column == "descriptive":
        descriptive(df1)
        sys.exit()

    if args.set == "obs":
        byPlayer(df1)
        sys.exit()

    if not args.column:
        my_feature = "subtype"
        print("Default feature:", my_feature)

    print("Default feature:", my_feature)
    token = main(my_feature, df1)
    if args.column == "specific":
        ask = input("\n\nRemove player label? y/n\n\n")
        if ask=="y":
            token = delete_player_label(token)

    # For the entire dataset, even if byPlayer() was chosen:
    my_2ng = bigram(token, df1)
    investigate_ngram(my_2ng, 2)
    my_3ng = trigram(token, df1)
    investigate_ngram(my_3ng, 3)









