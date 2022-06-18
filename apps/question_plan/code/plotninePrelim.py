
################################################################
'''
Creator: Salena Torres Ashton
Date:    20 May 2022
Purpose: plotnine() and ToMCAT work

    This is a tutorial I put together from my notes in R,
    Python, coursework and things I've found on the Internet

    Plot in Python using the same grammar as ggplot()
'''
################################################################

import numpy
import matplotlib.pyplot as pyplot
import pandas
from plotnine import *




# Read in the data and remove nulls or nas #####
raw = pandas.read_csv("../data/causalLabels.csv")
print("Type of raw data:", type(raw))
print("\nColumns in the data:\n")
for col in raw.columns:
    print("\t", col)

# Describe statistics for numerical data of raw data:
print("\nDescribe raw data:\n", raw.describe())


### NOTE: to print using plotnine() in a script, not a notebook:
    # Don't use pyplot.show()
    # Use print(name of plot figure)
    # Plot the data using python version of ggplot()
figureName = (ggplot(raw, 
                     aes("questionVerb", "questionNoun")) +
              geom_point() +
              facet_wrap("~video") # tilda goes inside quotes now.
        )

print(figureName)




print("\n\n", "-"*60, "\n\n")
################################################################
