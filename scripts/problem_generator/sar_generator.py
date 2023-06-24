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

Notes:
    Currently I'm working on objects only.
    TODO: object generation, then continue with initial states and htn
    sections.
"""

import argparse
import sys
import random


def get_objects(n_players, n_victims, n_markerTypes, n_rooms, n_rubble):
    """
    Purpose:
        Generates objects section of the problem file. The number of each
        objects are specified in the the command line.

    Arguments:
        n_players: number of players
        n_victims: number of victims
        n_markerTypes: number of markerTypeing locations, if they differ from victim
        n_rooms:  number of rooms that are a final destination
        n_rubble: Rubble found in rooms. This argument might be temporary.

    Returns:
        A string of objects

    Example of imitated output:
        (:objects
            player1 player2 - player
            victim1 victim2 - victim
            markerType1 markerType2 - markerType
            room1 - room
        )
    """

    s = "(:objects\n"
    s = "{}\n\t{}".format(s, get_obj_line(n_players, "player"))
    s = "{}\n\t{}".format(s, get_obj_line(n_victims, "victim"))
    s = "{}\n\t{}".format(s, get_obj_line(n_markerTypes, "markerType"))
    s = "{}\n\t{}".format(s, get_obj_line(n_rooms, "room"))
    s = "{}\n\t{}".format(s, get_obj_line(n_rubble, "rubble"))
    return s + "\n)"


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


def main():
    """
    Purpose:
        Problem generation begins here, using command-line arguments and naming
        the file in a player-victim-room numbering format. This naming
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
    parser.add_argument("-r", help="rooms", required=True, type=int)
    parser.add_argument("-x", help="rubble", required=False, type=int)
    args = parser.parse_args()

    n_players = args.p
    n_victims = args.v
    n_markerTypes = args.m
    n_rooms = args.r
    n_rubble = args.x

    if n_rooms < 1 or n_victims < 1 or n_players < 1:
        print("You need at least one room, one player and one victim.")
        exit(1)

    problem_name = "p-{}-{}-{}".format(n_players, n_victims, n_rooms)

    print("(define (problem " + problem_name + ")")
    print("(:domain sar3)")
    print(get_objects(n_players, n_victims, n_markerTypes, n_rooms, n_rubble))
    print(")")


if __name__ == "__main__":
    main()
