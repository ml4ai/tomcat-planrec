#!/usr/local/bin/python3
"""
Purpose:
    Generates problems from the sar domain. This program is based off of an
    example I've taken from
    https://github.com/panda-planner-dev/ipc2020-domains/tree/master/partial-order/Barman-BDI.

Created:
    24 June 2023

Updated:
    24 June 2023

Functions in this File:
    get_objects()
    get_obj_line()
    get_atom_line()
    get_init()
    main()

Functions needed for this File:
    get_htn()

Notes:
    * Right now it initializes with the same number of players, victims and
    locations. This is temporary so I can shuffle or randomize the players tending
    to different victims.

"""
#------------------------------------------------------------------------------

import argparse
import sys
import random

#------------------------------------------------------------------------------
def get_objects(n_players, n_victims, n_markerTypes, n_locations, n_rubble):
    """
    Purpose:
        Generates objects section of the problem file. The number of each
        objects are specified in the the command line.

    Arguments:
        n_players: number of players
        n_victims: number of victims
        n_markerTypes: number of markerTyping locations, if they differ from victim
        n_locations:  number of locations that are a final destination
        n_rubble: Rubble found in locations. This argument might be temporary.

    Returns:
        A string of objects

    Example of output:
        (:objects
            player1 player2 - player
            victim1 victim2 - victim
            markerType1 markerType2 - markerType
            location1 - location
        )
    """

    s = "\t(:objects"
    s = "{}\n\t\t{}".format(s, get_obj_line(n_players, "player"))
    s = "{}\n\t\t{}".format(s, get_obj_line(n_victims, "victim"))
    s = "{}\n\t\t{}".format(s, get_obj_line(n_markerTypes, "markerType"))
    s = "{}\n\t\t{}".format(s, "sickbay_A sickbay_B sickbay_C - location")
    s = "{}\n\t\t{}".format(s, "sos novictim regularvictim criticalvictim threat abrasion boneabrasion rubble_marker - marker_type")
    s = "{}\n\t\t{}".format(s, get_obj_line(n_locations, "location"))
    s = "{}\n\t\t{}".format(s, get_obj_line(n_rubble, "rubble"))
    return s + "\n\t)"

#------------------------------------------------------------------------------
def get_obj_line(n, name):
    """
    Purpose:
        This function generates a line of object declarations for a specific
        type of object in the HDDL domain. It is a helper function for
        get_objects().

    Arguments:
        n: number of objects
        name: name of object type
    """

    line = ""
    for i in range(1, n + 1):
        line = line + "{}{} ".format(name, i)
    return line + "- {}".format(name)


#------------------------------------------------------------------------------
def get_atom_line(*args):
    """
    Purpose:
        This function generates a formatted atom line for a given predicate and
        its arguments.

    Arguments:
        A variable number of sting arguments that represent the predicate and
        its argument value.

    For Example:
        input: 'get_atom_line("healed", "victim1")
        output: (healed victim1)'

    Returns:
        A formatted predicate.
    """

    return "({})".format(" ".join(args))


#------------------------------------------------------------------------------
def get_init(n_players, n_victims, n_markerTypes, n_locations, n_rubble):
    """
    Purpose:
        Generate the initial state of the problem file. This initializes
        various predicates and their states.

    Arguments:
        n_players: number of players
        n_victims: number of victims
        n_markerTypes: number of markerTyping locations, if they differ from victim
        n_locations:  number of locations that are a final destination
        n_rubble: Rubble found in locations. This argument might be temporary.

    Returns:
        A string of initialized states for the predicates.

    Example of output:
        (:init
        )

    Notes:
        * The following predicates are good for prelimary initialization. As
        this domain develops, this function will increase in complexity:
                (unconscious ?arg0 - victim)
                (at ?arg0 - human ?arg1 - location)
                (present ?arg0 - rubble ?arg1 - location)
                (medic ?arg0 - player)
                (engineer ?arg0 - player)
                (transporter ?arg0 - player)
                (sos ?arg0 - marker_type)
                (regularvictim ?arg0 - marker_type)
                (criticalvictim ?arg0 - marker_type)
                (abrasion ?arg0 - marker_type)
                (bonedamage ?arg0 - marker_type)
                (rubble_marker ?arg0 - marker_type)
                (threat ?arg0 - marker_type)
                (vic_is_type_A ?arg0 - victim)
                (vic_is_type_B ?arg0 - victim)
                (vic_is_type_C ?arg0 - victim)
                (sb_is_type_A ?arg0 - location)
                (sb_is_type_B ?arg0 - location)
                (sb_is_type_C ?arg0 - location)
        * The following predicates are not represented in this function since
        they tend to start as false and turn true during the mission:
                (rescued_r ?arg0 - victim)
                (rescued_c ?arg0 - victim)
                (holding ?arg0 - player)
                (held ?arg0 - player ?arg1 - victim)
                (healed ?arg0 - victim)
                (novictim ?arg0 - marker_type)
                (sos ?arg0 - marker_type)
                (abrasion ?arg0 - marker_type)
                (bonedamage ?arg0 - marker_type)
                (diagnosed_A ?arg0 - victim)
                (diagnosed_B ?arg0 - victim)
                (diagnosed_C ?arg0 - victim)
                (marker_at ?arg0 - player ?arg1 - marker_type ?arg2 -   location)
    """

    s = "\t(:init "

    # Assign players to role within the mission
    s = "{}\n\t\t{}".format(s, get_atom_line("medic", "player1"))
    s = "{}\n\t\t{}".format(s, get_atom_line("transporter", "player2"))
    s = "{}\n\t\t{}".format(s, get_atom_line("engineer", "player3"))

    # Temporary placeholders for novictim and sos marker types
    s = "{}\n\t\t{}".format(s, get_atom_line("SOS", "sos"))
    s = "{}\n\t\t{}".format(s, get_atom_line("novictim", "novictim"))

    # For now, assume victim 1 is a critical victim at the beginning.
    s = "{}\n\t\t{}".format(s, get_atom_line("unconscious", "victim1")) + "\n"

    # Randomize players, victims and location locations.
    #TODO: Right now it initializes as the same number of players, victims and
        # Rooms. This will need to be changed soon.
    players = list(range(1, n_players + 1))
    victims = list(range(1, n_victims + 1))
    rubbles= list(range(1, n_rubble + 1))
    locations = list(range(1, n_locations + 1))

    random.shuffle(players)
    random.shuffle(victims)
    random.shuffle(locations)

    for i in range(n_victims):
        s = "{}\t\t{}".format(s, get_atom_line("at", "victim{}".format(victims[i]), "location{}".format(locations[i]))) + "\n"

    for i in range(n_players):
        s = "{}\t\t{}".format(s, get_atom_line("at", "player{}".format(players[i]), "location{}".format(locations[i]))) + "\n"

    for i in range(n_rubble):
        s = "{}\t\t{}".format(s, get_atom_line("present",
                                               "rubble{}".format(rubbles[i]), "location{}".format(locations[i]))) + "\n"

    # Randomize the type of victim we have.
    types = ["A", "B", "C"]   # Three types of victims and sickbays possible.
    for i in range(n_victims):
        t = random.choice(types)
        s = "{}\t\t{}".format(s, get_atom_line("vic_is_type_" + t, "victim{}".format(victims[i]), )) + "\n"

    # Assign victim types to sickbay types.
    s = "{}\t\t{}".format(s, get_atom_line("sb_is_type_A", "sickbay_A"))
    s = "{}\n\t\t{}".format(s, get_atom_line("sb_is_type_B", "sickbay_B"))
    s = "{}\n\t\t{}".format(s, get_atom_line("sb_is_type_C", "sickbay_C"))

    return s + "\n\t)"


#------------------------------------------------------------------------------
def main():
    """
    Purpose:
        Problem generation begins here, using command-line arguments and naming
        the file in a player-victim-location numbering format. This naming
        format should be changed during development.

    Arguments:
        none

    Notes about domain:
        * Marker types are not required for problem generation.
        * Rubble specification not required for problem generation, but it's
        nice to have for testing.
    """

    parser = argparse.ArgumentParser()
    parser.add_argument("-p", help="players", required=True, type=int)
    parser.add_argument("-v", help="victims", required=True, type=int)
    parser.add_argument("-m", help="markerTypes", required=False, type=int)
    parser.add_argument("-r", help="locations", required=True, type=int)
    parser.add_argument("-x", help="rubble", required=False, type=int)
    args = parser.parse_args()

    n_players = args.p
    n_victims = args.v
    n_markerTypes = args.m
    n_locations = args.r
    n_rubble = args.x

    if n_locations < 1 or n_victims < 1 or n_players < 1:
        print("You need at least one location, one player and one victim.")
        exit(1)

    problem_name = "p-{}-{}-{}".format(n_players, n_victims, n_locations)

    print("(define (problem " + problem_name + ")")
    print("\t(:domain sar3)")
    print(get_objects(n_players, n_victims, n_markerTypes, n_locations, n_rubble))
    print(get_init(n_players, n_victims, n_markerTypes, n_locations, n_rubble))
    print(")")


#------------------------------------------------------------------------------
if __name__ == "__main__":
    main()
