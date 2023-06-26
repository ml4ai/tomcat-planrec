#!/usr/local/bin/python3
"""
Purpose:
    Generates problems from the sar domain. This program is based off of an
    example I've taken from
    https://github.com/panda-planner-dev/ipc2020-domains/tree/master/partial-order/Barman-BDI.

Created:
    24 June 2023

Updated:
    25 June 2023

Functions in this File:
    get_objects()
    get_obj_line()
    get_atom_line()
    get_init()
    main()
    get_task()
    get_htn()

Notes:
    TODO: parameters for the htn section

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
                (diagnosed_A ?arg0 - victim)
                (diagnosed_B ?arg0 - victim)
                (diagnosed_C ?arg0 - victim)
                (marker_at ?arg0 - player ?arg1 - marker_type ?arg2 - location)
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
    players = list(range(1, n_players + 1))
    victims = list(range(1, n_victims + 1))
    rubbles = list(range(1, n_rubble + 1))
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
def get_task(n_players, n_victims, n_markerTypes, n_locations, n_rubble):
    """

    """
    ###  THIS IS EVERYTHING THAT I WANT TO REPEAT FOR EACH TASK GENERATED  ###

    tasks = {
        "go_break_rubble": ['player1', 'rocks', 'pos', 'room'],
        "evacuate_victim": ['player1', 'victim', 'room', 'sickbay'],
        "go_triage_victim": ['player1', 'victim', 'pos', 'room'],
        "go_pickup_victim": ['player1', 'victim', 'pos', 'room'],
        "transport_victim": ['player1', 'victim', 'pos', 'room'],
        "carry_victim": ['player1', 'victim', 'pos', 'room'],
        "wake_triage_critical": ['player1', 'player2', 'victim', 'final'],
        "go_transport_victim": ['player1', 'victim', 'pos', 'room', 'final'],
        "gather_to_wake": ['player1', 'player2', 'victim', 'pos', 'room', 'final'],
        "gather_wake_evacuate": ['player1', 'player2', 'victim', 'pos', 'room', 'final', 'sickbay'],
        "gather_teammate": ['player1', 'player2', 'player3', 'pos1', 'pos2', 'pos3', 'room']
    }

    players = list(range(1, n_players + 1))
    victims = list(range(1, n_victims + 1))
    locations = list(range(1, n_locations + 1))
    random.shuffle(locations)
    random.shuffle(victims)

    # Randomly choose a task.
    chosen_task = random.choice(list(tasks.keys()))

    # Randomly assign arguments. Remember that I only want the name of the task
    # and the value of the argument, not the name of the argument itself.
    arguments = {}
    values = {}
    for arg in tasks[chosen_task]:
        if 'pos' in arg:
            value = "location" + str(random.choice(locations))
            arguments[arg] = value
        elif 'room' in arg:
            value = "location" + str(random.choice(locations))
            arguments[arg] = value
        elif 'final' in arg:
            value = "location" + str(random.choice(locations))
            arguments[arg] = value
        elif 'player' in arg:
            arguments[arg] = arg
        elif 'victim' in arg:
            value = "victim" + str(random.choice(victims))
            arguments[arg] = value
        else:
            arguments[arg] = f"pos{random.randint(1, 3)}"

    s = "\n\t\t\t({}".format(chosen_task)
    for arg in arguments.values():
        s = "{} {}".format(s, arg)

    return s + ")\t"
#------------------------------------------------------------------------------


def get_htn(n_players, n_victims, n_markerTypes, n_locations, n_rubble, n_htns):
    """
    Purpose:
        Generates the HTN task section of the problem file.

    Arguments:
        n_players: number of players
        n_victims: number of victims
        n_markerTypes: number of markerTyping locations, if they differ from victim
        n_locations:  number of locations that are a final destination
        n_rubble: Rubble found in locations. This argument might be temporary.

    Returns:
        parameters and subtasks string for the htn section of the problem file.

    Example of output:
        (:htn
            :parameters ()
            :subtasks (and
                (task1 arg0 arg1 arg2)
                (task2 arg0 arg1))
        )
    Notes:
        * For now: List of possible tasks that can be randomly selected.

    """
    ### This is the start of the htn section THAT I DON'T WANT TO REPEAT! ###
    s = "\t(:htn\n\t\t:parameters ()"

    args_list = ""     # to paste for single task problem files only.
    for n in range(n_htns):
        temp = get_task(n_players, n_victims, n_markerTypes, n_locations, n_rubble)
        args_list = "{} {}".format(args_list, temp)

    if n_htns > 1:
        s = s + "\n\t\t:subtasks (and"
        s = "{} {}".format(s, args_list)
        return s + "\n\t\t\t\t\t)\n\t)"
    else:
        a_list = ":subtasks" + args_list
        s = "{}\n\t\t{}".format(s, a_list)
        return s + "\n\t)"

#------------------------------------------------------------------------------

def hardcoding_htn():
    s = "\t(:htn\n\t\t:parameters ()"
    s = s + "\n\t\t:subtasks (and"

    #for i in range(min(n_players, n_victims)):
    #    s = "{}\n\t\t(salena_task player{} victim{})".format(s, players[i], victims[i])

    #print("\nCurrent Victim List:", victims)
    #TODO: Locations are merely a placeholder for now. I need to talk with the
       # planning team to discuss how many of these tasks I should code up--STA
       # 24June2023
    for i in range(n_players):
        v = victims.pop()
        a = random.choice(locations)
        b = random.choice(locations)
        #print("\n\tAfter 1st pop Current Victim List:", victims)
        s = "{}\n\t\t\t(carry_victim player{} victim{} location{} location{})".format(s, players[i], v, a, b)

    return s + "\n\t\t\t)\n\t)"

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

    # TODO: Now we add the number of HTNs we want to generate.
            # At this time, ordered HTNS do not make sense. In progress.
    parser.add_argument("-t", help="htns", required=False, type=int)
    args = parser.parse_args()

    n_players = args.p
    n_victims = args.v
    n_markerTypes = args.m
    n_locations = args.r
    n_rubble = args.x
    n_htns = args.t

    if n_locations < 1 or n_victims < 1 or n_players < 1:
        print("You need at least one location, one player and one victim.")
        exit(1)

    problem_name = "p-{}-{}-{}".format(n_players, n_victims, n_locations)

    print("(define (problem " + problem_name + ")")
    print("\t(:domain sar3)")
    print(get_objects(n_players, n_victims, n_markerTypes, n_locations, n_rubble))
    print()
    print(get_init(n_players, n_victims, n_markerTypes, n_locations, n_rubble))
    print()
    print(get_htn(n_players, n_victims, n_markerTypes, n_locations, n_rubble, n_htns))
    print(")")


#------------------------------------------------------------------------------
if __name__ == "__main__":
    main()
