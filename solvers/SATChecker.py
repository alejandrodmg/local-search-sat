#!/usr/bin/env python

import re
import functools
import operator

def load_cnf(instance):
    """
    1 - It first reads a given .cnf file and drops newline characters.
    2 - If the line starts with %, then break the loop as all clauses have been stored.
    3 - If the line starts with p, then it's the problem definition.
    4 - If the line contains numbers and not letters, then it's a clause.
       Extracts from evey line pos/neg number characters/strings and convert them to integer.
    """
    ## 1 ##
    with open(instance) as f:
        lines = [line.rstrip('\n') for line in f]
    f.close()
    clauses = []
    for l in lines:
        ## 2 ##
        if l.startswith('%'):
            break
        ## 4 ##
        elif bool(re.search(r'\d+', l)) and not bool(re.search(r'[a-zA-Z]', l)):
            new_clause = list(map(int, re.findall(r'-?[1-9][0-9]|-?[1-9]', l)))
            clauses.append(new_clause)
        ## 3 ##
        elif l.startswith('p'):
            problem = re.findall(r'\d+', l)

    return clauses, int(problem[0])


def load_solution(solution):
    """
    1. It first reads a given .text solution file and drops newline characters.
    2. If the line starts with 'v' and it contains pos/neg number characters
       or 0 values, then it's a variable line. Store the assignments if True.
    3. Finally, the list gets flattened.
    """
    ## 1 ##
    with open(solution) as f:
        lines = [line.rstrip('\n') for line in f]

    assignments = []
    for l in lines:
        ## 2 ##
        if l.startswith('v') and bool(re.search(r'-?\d+', l)):
            assignments.append(list(map(int, re.findall(r'-?[1-9][0-9]|-?[1-9]', l))))
    ## 3 ##
    assignments = functools.reduce(operator.iconcat, assignments, [])
    print('Successfully read a candidate solution with {} variables.'.format(len(assignments)))

    return assignments


def SAT(solution, cnf, return_clauses=True):
    """
    This is the actual implementation of the SAT checker.

    :param solution: A set of 'Boolean' variables in the form of pos/neg int numbers.
    :param cnf: A set of clauses in conjunctive normal form.
    :param return_clauses: Return a list of True or False assignment for each clause
    :return: List of Boolean variables that indicates the clauses that are satisfied (True) and
            unsatisfied (False). Additionally, this function prints the number of unsatisfied clauses.
    """

    sat = []
    for clause in cnf: # for each clause in the CNF:
        is_sat = False # the clause is initially False until this loop verifies it.
        for literal in clause: # for each literal in the clause:
            if literal in solution: # if the literal has the same assignment as the variable in the candidate solution.
                is_sat = True # the clause is SAT.
                sat.append(is_sat)
                break # stop checking other literals in this clause.
        if not is_sat: # if is_sat remains False:
            sat.append(is_sat) # the clause is UNSAT.
    unsat = len(sat) - sum(sat) # calculate the total number of UNSAT clauses.

    if return_clauses: # if True:
        return int(unsat), sat # return the number of UNSAT clauses and a list of boolean values indicating
        # which clauses are SAT or UNSAT.
    else:
        return int(unsat)
