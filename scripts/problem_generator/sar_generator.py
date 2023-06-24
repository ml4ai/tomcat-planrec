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


def get_objects(n_players, n_victims, n_starts, n_rooms):
    """
    Purpose:
        Generates objects section of the problem file. The number of each
        objects are specified in the the command line.

    Arguments:
        n_players: number of players
        n_victims: number of victims
        n_starts: number of starting locations, if they differ from victim
        n_rooms:  number of rooms that are a final destination

    Returns:
        A string of objects

    Example of imitated output:
        (:objects
            player1 player2 - player
            victim1 victim2 - victim
            start1 start2 - start
            room1 - room
        )
    """

    s = "(:objects\n"
    s = "{}\n\t{}".format(s, get_obj_line(n_players, "player"))
    s = "{}\n\t{}".format(s, get_obj_line(n_victims, "victim"))
    s = "{}\n\t{}".format(s, get_obj_line(n_starts, "start"))
    s = "{}\n\t{}".format(s, get_obj_line(n_rooms, "room"))
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
        the file in a player-victim-starts-room numbering format. This naming
        format should be changed during development.

    Arguments:
        none
    """

    parser = argparse.ArgumentParser()
    parser.add_argument("-p", help="players", required=True, type=int)
    parser.add_argument("-v", help="victims", required=True, type=int)
    parser.add_argument("-s", help="starts", required=True, type=int)
    parser.add_argument("-r", help="rooms", required=True, type=int)
    args = parser.parse_args()

    n_players = args.p
    n_victims = args.v
    n_starts = args.s
    n_rooms = args.r

    if n_rooms < 1 or n_victims < 1 or n_players < 1:
        print("You need at least one room, one player and one victim.")
        exit(1)

    problem_name = "p-{}-{}-{}-{}".format(n_players, n_victims, n_starts, n_rooms)

    print("(define (problem " + problem_name + ")")
    print("(:domain sar3)")
    print(get_objects(n_players, n_victims, n_starts, n_rooms))
    print(")")


if __name__ == "__main__":
    main()
