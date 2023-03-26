import pandas
from collections import Counter

# For ease in reading terminal output:
hrule = ("\n"+"-"*80+"\n")
pandas.set_option('display.max_rows', 50000)
pandas.set_option('display.max_columns', 50000)
pandas.set_option('display.width', 600)

#------------------------------------------------------------------
# Load data
df = pandas.read_csv("../data/total_601_804.csv")
print(hrule, "Final number of Rows:", len(df.index))


# Subset dataframe so that I get string value of interest, the line before it
# and the line after it.

#------------------------------------------------------------------
#### Use this mask for any kind of awakened value when proximity block interaction
   ### is triggered
#mask = df["awake"].isin(["awakened", "not_awakened"])

#### Use this mask if you want only the awakened value.
mask = df["awake"].isin(["awakened"])

# Number of lines before and after each awakened value observation:
line_buffer = 3
mask_before = mask.shift(line_buffer, fill_value = False)
mask_after = mask.shift(-line_buffer, fill_value = False)
proximity_block = df[mask | mask_before | mask_after]
print(proximity_block.head(3000))


#------------------------------------------------------------------
# Investigate most common Markov Chain Sequence
pattern_length = 2
block = pandas.Series(proximity_block["subtype"])
# create a list of tuples containing each unique pattern sequence and its frequency count
patterns = Counter()
for i in range(len(block)-pattern_length):
    pattern = tuple(block[i:i+pattern_length])
    if pattern[0] != pattern[1]:
        patterns[pattern] += 1
patterns = patterns.most_common()

# extract the most common pattern sequence
most_common_pattern = patterns[0][0]

print("The most common pattern in the pandas Series is:", most_common_pattern)

n = 5  # number of top patterns to print
for i in range(n):
    pattern = patterns[i][0]
    count = patterns[i][1]
    print(f"{i+1}. Pattern: {pattern}, Count: {count}")

