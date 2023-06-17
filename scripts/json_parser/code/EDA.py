"""
Created by: Salena Ashton
Date Created: 25 March 2023
Last Upandasted: 25 March 2023

Purpose:
    * Investigate proximity block interaction sequences so that tasks designed
    in HDDL domain will reflect data-driven sequences.

"""
import pandas
from collections import Counter

# For ease in reading terminal output:
hrule = ("\n"+"-"*80+"\n")
pandas.set_option('display.max_rows', 50000)
pandas.set_option('display.max_columns', 50000)
pandas.set_option('display.width', 600)

#------------------------------------------------------------------
# Load data
df = pandas.read_csv("../data/total_7_secondDecay_601_804.csv")
print(hrule, "Final number of Rows:", len(df.index))
df = df.drop(columns=['Unnamed: 0'])
print(list(df.columns))


# Subset dataframe so that I get string value of interest, the line before it
# and the line after it.

#------------------------------------------------------------------
#### Use this mask for any kind of awakened value when proximity block interaction
   ### is triggered
#mask = df["awake"].isin(["awakened", "not_awakened"])

#### Use this mask if you want only the awakened value.
mask = df["awake"].isin(["awakened"])

# Number of lines before and after each awakened value observation:
line_buffer = 4
mask_before = mask.shift(line_buffer, fill_value = False)
mask_after = mask.shift(-line_buffer, fill_value = False)
proximity_block = df[mask | mask_before | mask_after]
print(proximity_block.tail(30))


#------------------------------------------------------------------
# Investigate most common Markov Chain Sequence
pattern_length = 4
block = pandas.Series(proximity_block["subtype"])
patterns = Counter()
total_occurrences = 0

# Count the occurrences of each pattern
for i in range(len(block) - pattern_length):
    pattern = tuple(block[i:i + pattern_length])
    ### If we don't want the first items to match:
    #if pattern[0] != pattern[1]:
    ### if we don't want the first three to match:
    if (pattern[0] != pattern[1]) & (pattern[1] != pattern[2]):
    ### If we don't care whether items match (unindent)
        patterns[pattern] += 1
        total_occurrences += 1

# Normalized count for each pattern
normalized_counts = []
for pattern, count in patterns.items():
    normalized_counts.append((pattern, count/total_occurrences))

def sort_key(x):
    return x[1]

normalized_counts = sorted(normalized_counts, key = sort_key, reverse = True)

# Extract the most common pattern and its normalized count
most_common_pattern = normalized_counts[0][0]
most_common_count = normalized_counts[0][1]

print(hrule)

n = 8  # number of top patterns to print
for i in range(n):
    pattern = normalized_counts[i][0]
    normalized_count = normalized_counts[i][1]
    print(f"{i+1}. Pattern: {pattern}, \n\tNormalized Count: {round(normalized_count, 3)}\n")

print(block.value_counts(normalize = True))
#------------------------------------------------------------------
