"""
Author:
    Salena Torres Ashton
    School of Information, University of Arizona

Created:
    19 July 2022

Last Updated:
    19 July 2022

Purpose:

"""

import json
import pandas
import time
from pprint import pprint
from datetime import date, timedelta


"""
Read processed metadata file into this program

Extract the player and raw text utterance

Set extractions into a dataframe and clean the data
"""

filename = open('pretty_638.json', 'r')
count = 0

text = []

while True:
    line = filename.readline()

    if not line:
        break

    #if "participant_id" in line:
    #    if "Server" not in line:
    #        text.append(line)

    if "text" in line:
        if "Victim Type" not in line:
            if " Victim Detected" not in line:
                text.append(line)

filename.close()


#t1 = ' '.join(text).replace(" ", "")

t1 = [sub.replace('\"', '') for sub in text]
t1 = [sub.replace(',', '') for sub in t1]
t1 = [sub.replace('text:', '') for sub in t1]
t1 = [sub.replace('participant_id:', '') for sub in t1]
t1 = [sub.replace('_ASIST3', '') for sub in t1]

for t in t1:
    print(t)

df = pandas.DataFrame(t1)
df.to_csv("./dataFrame_638.csv")
