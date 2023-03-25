
# TODO: line 150ish uses the 10-second heuristic for mapping labels to actions. 
"""
--------------------------------------------------------------------------
Purpose:
    Action sequence and mapping dialog acts to action(s).

    This file explores data collected by Salena Torres Ashton for the Theory
    of Mind-based Cognitive Architecture for Teams (ToMCAT), PI: Adarsh
    Pyarelal.

    This script:
        * parses metadata from video observations that were collected using MQTT
        * extracts needed message files from each observation
        * Demostrates code using only two observations
        * Saves each extracted observation into its own csv file
        * Concatenates all observations into one large csv file for analysis
        * Leads to use of the machine learning and NLP script for the final paper.
        * This final paper is an extension of INFO 514 Homework 1 and 3.

Author:
    Salena T. Ashton
    PhD Student, School of Information
    University of Arizona

Date Created:
    28 November 2022

Updated:
    25 March 2023


Affiliation:
    Theory of Mind-based Cognitive Architecture for Teams (ToMCAT)
    ASIST Program (DARPA)
    Adarsh Pyarelal, PI
    School of Information;  University of Arizona

--------------------------------------------------------------------------
"""

import json
from pprint import pprint
import pandas
import random
from datetime import date, time, datetime
from dateutil.relativedelta import relativedelta
from dateutil.parser import parse

# For ease in reading terminal output:
hrule = ("\n"+"-"*80+"\n")
textfilename_list = []
pre_df = pandas.DataFrame(textfilename_list)
df2 = pandas.DataFrame(textfilename_list)
pandas.set_option('display.max_rows', 50000)
pandas.set_option('display.max_columns', 50000)
pandas.set_option('display.width', 600)

# Functions to facilitate use of timestamp
def float_ms(microseconds):
    ms = str(microseconds) 
    return (int(ms[:1])/10)

def get_time(one):
    a = (one.hour*3600 + one.minute*60 + one.second +
            float_ms(one.microsecond))
    return(round(a, 3))

obs_list = []
for i in range(631, 701):
    j = str(i)
    obs_list.append(j)
    digit = j
    filename = ("../data/raw"+digit+".metadata")
    list_dict = []

    # Default settings for messages that do not have dialog events
    rule = ""
    text = ""
    label = ""
    # Most specific level of the label list
    specific = ""

    # In order to map dialog rules and labels to other topics, we loop through the
        # next action from the message bus with the old assignment of rule and
        # label. In most cases, this logic is valid for the same player who
        # triggered the dialog event. However, if too much time has passed between
        # dialog events, the rules and labels are set back to 'none.'
    time_passed = 0
    old_timestamp = 0
    dialog_player = "no_one"
    awake = "na"
    p_range = "na"

    try:
        with open(filename) as f:
            for i, line in enumerate(f):
                message = json.loads(line) #message is concept and a dict
                if not "topic" in message:
                    t = "noTopic"
                else:
                    t = message["topic"]                # topic is a string
                if not t in ("observations/events/player/freeze",
                         "observations/events/player/itemdrop",
                        "observations/events/player/itempickup",
                        "observations/events/player/itemuse",
                        "observations/events/player/location",
                        "observations/events/player/marker_placed",
                        "observations/events/player/marker_removed",
                        "observations/events/player/proximity_block",
                        "observations/events/player/rubble_collapse",
                        "observations/events/player/rubble_destroyed",
                        "observations/events/player/tool_used",
                        "observations/events/player/tool_depleted",
                        "observations/events/player/triage", 
                        "observations/events/player/victim_evacuated",
                        "observations/events/player/victim_picked_up",
                        "observations/events/player/victim_placed",
                        "agent/dialog"):
                    continue
                topic = t.replace("observations/events/player/", "")
                timestamp = get_time(parse(message["msg"]["timestamp"]))
                player = message["data"]["participant_id"]
                # Not all messages have awake, so get the placeholder first.
                if "awake" in message.get("data", {}):
                    awake_value = message["data"]["awake"]
                    # since players aren't efficient in waking critical
                    # victims, keep track of their range regardless of awakened
                    # state.
                    p_range = message["data"]["players_in_range"]
                    if awake_value:
                        awake = "awakened"
                    else:
                        awake = "not_awakened"
                s = message["msg"]['sub_type']
                subtype = s.replace("Event:", "")
                if "dialogue_event" in subtype:
                    dialog_player = player
                    time_passed = ""
                    old_timestamp = timestamp
                else:
                    # This is assigned when too much time passed or there was some
                        # dialog event with no utterance.
                    time_passed = abs(round((old_timestamp - timestamp),3))
                    if time_passed > 10:
                        rule = "cannot_justify"
                        specific = "cannot_justify"

                if "location" in topic:
                    subtype = "room_change"

                text = "no_text"
                timer = "no_timer"
                if "mission_timer" in message["data"]:
                    timer = (message["data"]["mission_timer"])
                #Create my list of dictionaries:
                list_dict.append({"obs":digit,
                                "time_passed":time_passed,
                                "topic":topic,
                                "timestamp":timestamp,
                                "player":player,
                                "p_range":p_range,
                                "awake":awake,
                                "dialog_player":dialog_player,
                                "subtype":subtype,
                                "rule":rule,
                                #"label":label,
                                "specific":specific,
                                "text":text,
                                "mission_timer":timer})

                if "extractions" in message["data"]:
                    ext = message["data"]["extractions"]
                    data = message["data"]
                    text = message["data"]["text"]
                    # to assign rule carryover, it must be the same player
                    if player == "Server":
                        #text.replace(text, text[9:])
                        #print(text[9:25])
                        text = text[9:25]
                        #print(text)
                        #text = text["text"]
                    #print(hrule, type(ext))
                    #print(hrule, "ext type:", type(ext))
                    #pprint(ext)
                    for e in ext:# turns back into a dict
                        #print(" -  "*20, "\n e type:", type(e))
                        #pprint(e)
                        label = e["labels"] # For list of labels
                        specific = e["labels"][0] # most specific label
                        # Generalize label
                        rooms= ["1", "2", "3", "4", "5", "6", "7", "8"]
                        for r in rooms:
                            if r in specific:
                                specific = "Room"
                        rule = e["rule"]
                        # Generalize rule
                        if "room" in rule:
                            rule = "room"
                        #print(rule)
                        list_dict.append({"obs":digit,
                                    "time_passed":time_passed,
                                    "topic":topic,
                                    "timestamp":timestamp,
                                    "player":player,
                                    "awake":awake,
                                    "p_range":p_range,
                                    "dialog_player":dialog_player,
                                    "subtype":subtype,
                                    "rule":rule,
                                    #"label":label,
                                    "specific":specific,
                                    "text":text,
                                    "mission_timer":timer})
                # Reset players_in_range and awake = "na" or they will persist falsly.
                awake = "na"
                p_range = "na"
        df = pandas.DataFrame(list_dict)#.set_index('timestamp')
        df.drop_duplicates(keep = False)
        #print(hrule, "OBS:", digit, "\n", df.head())
        #print("Number of rows:", len(df.index))
        textfilename = "finally_"+digit+".csv"
        df.to_csv(textfilename)
        df1 = [pre_df, df]
        df2 = pandas.concat(df1, axis = 0)
#        print(hrule, #"pre:", pre_df.head(2), pre_df.tail(2),
                #"\n\ndf:", df.head(2), df.tail(2),
                #"\n\ndf2:", df2.head(2), df2.tail(2),
#                "\n\ndf:", df2.head(),
#                "\nNumber of rows:", len(df2.index))
        textfilename_list.append(textfilename)
        pre_df = df2
    except:
        print("Observation "+digit+ " does not exist.")

print(hrule, df2, "Final number of Rows:", len(df2.index))
df2.to_csv("demo___total_631_700.csv")

#print(hrule, df2.head(2000))
# Investigate rule and subtype mapping to create HDDL domain:
subRule = df2[["subtype", "specific"]]
rule_givenSub = subRule.groupby('subtype').value_counts(normalize = True).to_frame()
rule_givenSub.reset_index(inplace = True)
rule_givenSub = rule_givenSub.rename(columns={0: 'conditional_probability'})

print(hrule, "Rule, Given Subtype of Event\n", rule_givenSub.head(40))
print(hrule, rule_givenSub.sort_values(by=['conditional_probability'], ascending = False).head(40))

print("Number of Observations:", len(textfilename_list))
for t in textfilename_list:
    print(t)

