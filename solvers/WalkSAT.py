#!/usr/bin/env python3

from SATChecker import load_cnf, SAT

import numpy as np
import random
import sys
from functools import reduce

from time import process_time
# Process-wide timing. CPU time in seconds as user + sys.
# API doc: https://docs.python.org/3/library/time.html
# Read more about this in: https://www.usenix.org/system/files/login/articles/08_beazley_034-038_online.pdf

setseed = 324218
random.seed(setseed)

class WalkSAT:
    def __init__(self, max_flips, max_tries, path_to_file, p, tl):
        """
        Initialize parameters and load CFN.
        """
        self.max_tries = max_tries
        self.max_flips = max_flips
        self.path_to_file = path_to_file
        self.p = p
        self.tl = tl
        self.tabu_tracking = {}
        self.cnf = []
        self.variables = -1
        self.output_best_assignment = []
        self.output_best_unsat = []
        self.var_dict = {}
        self.clau_dict = {}
        self.current_solution = []
        self.fitness = -1
        self.total_steps = 0
        self.total_restarts = -1

        self.load_sat_problem()

    def load_sat_problem(self):
        """
        Read an instance from a given a path.
        """
        cnf_instance = self.path_to_file
        self.cnf, self.variables = loadCNF(instance=cnf_instance)

    def random_truth_assignment(self):
        """
        Generate a random truth assignment for a SAT problem.

        :return: A random candidate solution for a CNF formula.
        """
        # the random assignment is sorted for readability.
        assignment = sorted(random.sample(range(1, self.variables + 1), self.variables))
        for variable in range(0, self.variables):
            # if a randomly generated boolean is True, then the variable
            # will be set to -v(False) else will remain True(+v).
            if bool(random.getrandbits(1)):
                assignment[variable] = assignment[variable] * (-1)

        return assignment

    def generate_dict_variables(self):
        """ Create a dictionary containing each variable (key) of the CNF, and the clauses where the variable
        is in (values).

        :return: A dictionary of variables and clauses of length equal to the number of variables.
        """
        dict_variables = {}
        for clause in self.cnf:
            for literal in clause:
                key = abs(literal)
                # setdeafult creates a new key (variable) if it doesn't already exists in the dictionary,
                # but if it does, then it'll simply append the clause where it's in.
                dict_variables.setdefault(key, []).append(clause)

        return dict_variables

    def generate_dict_clauses(self, unsat_bool_list):
        """ Generate a dictionary of the clauses as tuples (keys)
        and whether if the clause is SAT or UNSAT (values). This make us being more efficient
        when calculating the net gain given a subset of clauses.

        :param unsat_bool_list: A list of boolean values showing if a clause in index i of
        the CNF is currently SAT or UNSAT.
        :return: A dictionary of clauses (key) and boolean values (values).
        """
        keys = range(len(self.cnf))
        dict_clauses = {}
        for i in keys:
            # we use tuples instead of lists as the latest are not hashable.
            dict_clauses[tuple(self.cnf[i])] = unsat_bool_list[i]

        return dict_clauses

    def update_dict_clauses(self, subset_clauses, is_sat, return_dict=False):
        """ Update boolean values of a dictionary of clauses (keys) given their new SAT/UNSAT status (values)
        in a list. In this function the order of the clauses and the boolean values in the list matter.

        :param subset_clauses: The clauses affected due to flipping a variable.
        :param is_sat: A list of boolean values that contains if the clauses are SAT/UNSAT after the flip.
        :param return_dict: Return dictionary of clauses (default: False).
        :return: (Optional: the dictionary of clauses and whether if they're SAT or UNSAT)
        """
        k = 0 # use a counter to update the values of the dictionary with new boolean values.
        for clause in subset_clauses:
            self.clau_dict[tuple(clause)] = is_sat[k]
            k += 1
        if return_dict: # this is optional in case further pre-processing is required,
            return self.clau_dict
        else:
            pass

    def get_unsat_clauses(self):
        """ Filter a dictionary by value and get keys. For the WalkSAT algorithm, we're looking for UNSAT clauses
        at each iteration.

        :return: A list of current UNSAT clauses as tuples.
        """
        unsat_clauses = list(dict(filter(lambda elem: elem[1] == False, self.clau_dict.items())).keys())

        return unsat_clauses

    def query_current_unsat(self, subset_clauses):
        """ Count the number of current UNSAT clauses given a subset of clauses.

        :param subset_clauses: A list of lists containing clauses.
        :return: Int value. Number of current UNSAT clauses.
        """
        sat = []
        for i in subset_clauses:
            sat.append(self.clau_dict[tuple(i)])
        unsat = len(sat) - sum(sat)  # unsat clauses

        return unsat

    def split_sat_unsat(self, subset_clauses):
        """ Split list into SAT and UNSAT clauses given a subset of clauses.

        :param subset_clauses: A list of lists containing SAT and UNSAT clauses.
        :return: Two lists with SAT and UNSAT clauses separately.
        """
        sat = []
        unsat = []
        for clause in subset_clauses:
            if self.clau_dict[tuple(clause)] == True:
                sat.append(clause)
            else:
                unsat.append(clause)

        return sat, unsat

    def flatten_clauses(self, list_of_lists, index):
        """
        Perform a lambda reduction of a list of lists.

        :param list_of_lists: A list of lists containing clauses.
        :param index: The flip index selected in previous steps (Any of: 0-damage move, min positive gain or random selection)
        :return: A flatten list.
        """
        flatten_list = reduce(lambda x, y: x + y, list_of_lists[index])
        return flatten_list

    def perform_zero_damage_flip(self, flip_index, selected_clause, affected_clauses):
        """
        Perform a Zero-Dame flip (WalkSAT algorithm). After passing a flip index of a zero-damage
        variable, this function effectively flips the variable in the current solution, and counts the number of
        current UNSAT clauses where the variable is in, as these will be the number of SAT clauses after flipping it
        (net gain).

        :param flip_index: The index of the variable to flip in the selected clause.
        :param selected_clause: The UNSAT clause selected at the start of the loop.
        :param affected_clauses: The clauses affected due to flipping a variable.
        :return: 1) net gain of flipping the variable, 2) the literal that now shows its negation in the clause, and
        3) the UNSAT clauses that became SAT after flipping the variable.
        """
        # Flip the variable in the current solution
        literal = selected_clause[flip_index]
        self.current_solution[abs(literal) - 1] = self.current_solution[abs(literal) - 1] * (-1)

        # Query the current UNSAT clauses where the variable is in
        current_unsat_c = affected_clauses[flip_index][0]

        # negative gain has to be zero (this is a zero-damage move and no SAT clause can go UNSAT) (i.e. 0)
        # positive gain is the number of clauses that were UNSAT and now are SAT (i.e. all currently UNSAT clauses -> len(current_unsat_c))
        # positive gain = number of UNSAT clauses (before flipping) - number of UNSAT clauses (after flipping)
        # net gain (positive gain - negative gain) is then calculated as:
        net_gain = len(current_unsat_c) - 0  # (- 0) for readability

        return net_gain, literal, current_unsat_c

    def perform_flip(self, flip_index, selected_clause, affected_clauses, c_evaluation, neg_gains):
        """
        Flip a variable given a 'flip index' and a clause. Then evaluate the impact on the overall fitness (number of
        UNSAT clauses).

        :param flip_index: The index of the variable to flip in the selected clause.
        :param selected_clause: The UNSAT clause selected at the start of the loop.
        :param affected_clauses: The clauses affected due to flipping a variable.
        :param c_evaluation: A list of boolean values that indicates which clauses, where a variable is in, would
        become SAT or UNSAT after flipping it.
        :param neg_gains: A list containing the negative gain that would result from flipping a variable in
        the selected clause.
        :return: 1) net gain of flipping the variable, 2) the literal that now shows its negation in the clause,
        3) a list of clauses where the variable is in, and 4) a list of boolean values indicating if the clauses are
        SAT or UNSAT after flipping the variable.
        """
        # Flip the variable in the current solution
        literal = selected_clause[flip_index]
        self.current_solution[abs(literal) - 1] = self.current_solution[abs(literal) - 1] * (-1)

        # get all the clauses where the variable that just got flipped is in.
        clauses = self.flatten_clauses(affected_clauses, flip_index)
        # get the list of boolean values indicating which clause became SAT or UNSAT after flipping the variable.
        satisfiability = c_evaluation[flip_index]

        # Query the current UNSAT clauses where the variable is in.
        current_unsat_c = affected_clauses[flip_index][0]

        # positive gain is the number of clauses that were UNSAT and now are SAT (i.e. all currently UNSAT clauses -> len(current_unsat_c))
        # the negative gain was calculated previously and it's an input to this function.
        net_gain = len(current_unsat_c) - neg_gains[flip_index]

        return net_gain, literal, clauses, satisfiability

    def tabu_capabilities(self):
        """
        Tabu's efficient implementation: We'll be storing for each variable the earliest next iteration that
        the search algorithm will be able to select a variable (again).

        :return: A dictionary of variables (keys) and last time the variable was flipped (value).
        """
        # iteration number is initially set to -1 for all variables.
        dict_moves = dict(zip(self.var_dict.keys(), [-1] * self.variables))
        return dict_moves

    def update_tabu_list(self, var, iteration):
        """
        Update Tabu's variable tracker. A variable recently flipped will be available again in
        iteration (current iteration + Tabu Tenure).

        :param var: A variable that just got flipped.
        """
        self.tabu_tracking[abs(var)] = iteration + self.tl

    def exclude_tabu_variables(self, clause, iteration):
        """
        Exclude variables that are currently Tabu given a clause or list of literals.

        :param clause: A list/array/tuple of literals (i.e. a randomly selected UNSAT clause 'bc').
        :param iteration: Current iteration the algorithm is at.
        :return: A list of variables in the input clause that aren't Tabu (valid moves).
         """
        bc = []
        for literal in clause:
            if self.tabu_tracking[abs(literal)] < iteration:
                bc.append(abs(literal))

        return bc

    def init_search(self):
        """
        Actual implementation of the search and optimization process.

        :return: 1) The number of UNSAT clauses, 2) a candidate solution to the problem, 3) the number of search steps made,
        and 4) the number of restarts performed.
        """
        # placeholders:
        self.output_best_assignment = None
        self.output_best_unsat = len(self.cnf)

        for i in range(self.max_tries):
            # the search is initialize with -1 restarts, so if the algorithm finds a solution at the first try, restarts will be 0.
            self.total_restarts += 1

            random_assignment = self.random_truth_assignment() # generate a random truth assignment,
            self.current_solution = random_assignment # which becomes the current solution to the problem.
            # then, calculate the number of UNSAT clauses using the current solution and return these clauses.
            self.fitness, unsat_clauses = SAT(random_assignment, self.cnf, return_clauses=True)

            # fill the dictionaries that contribute to make an efficient implementation of the algorithm:
            self.var_dict = self.generate_dict_variables()
            self.clau_dict = self.generate_dict_clauses(unsat_bool_list=unsat_clauses)

            # initialize Tabu Search:
            self.tabu_tracking = self.tabu_capabilities()

            if self.fitness == 0: # if the random candidate solution is a solution to the problem then break the loop.
                print('All clauses were satisfied')
                return self.fitness, self.current_solution, self.total_steps, self.total_restarts

            for j in range(self.max_flips):
                self.total_steps += 1 # search steps counter

                # get number of UNSAT clauses and randomly select one of these
                current_unsat_clauses = self.get_unsat_clauses()
                sel_clause = random.choice(current_unsat_clauses)
                # exlcude variables that are Tabu from the selected clause
                bc = self.exclude_tabu_variables(clause=sel_clause, iteration=j)
                if not bc:
                    # if the list returned isn't populated because all the variables are Tabu,
                    # then we'll skip this iteration.
                    continue
                # create empty lists to store useful data.
                evaluation = []
                negative_gains = []
                sat_unsat_split = []
                for literal in bc: # for each literal in the selected UNSAT clause:
                    candidate_solution = self.current_solution.copy() # make of copy of the current solution.
                    # find the current assignment of the variable using the candidate solution's index.
                    variable = candidate_solution[abs(literal) - 1]
                    # flip variable to create a new candidate solution.
                    candidate_solution[abs(literal) - 1] = variable * (-1)

                    # query all the clauses where the variable is in using the dictionary of variables.
                    subset_var_clauses = self.var_dict[abs(variable)]
                    # get the split between SAT and UNSAT clauses using the dictionary of clauses and boolean values.
                    sat, unsat = self.split_sat_unsat(subset_var_clauses)

                    # compute the negative gain using a subset of clauses that could go UNSAT
                    # (we only need to compute this for current SAT clauses).
                    ng, bool_list = SAT(candidate_solution, sat, return_clauses=True)

                    # create a list of boolean values that indicates which clauses, where the variable is in, would
                    # become SAT or UNSAT after flipping it. We know that all the current UNSAT clauses will be SAT,
                    # so we can just do: ([True] * len(unsat)) instead of checking it.
                    eval = ([True] * len(unsat)) + bool_list

                    # store the results of each variable (maximum 3 variables).
                    negative_gains.append(ng)
                    evaluation.append(eval)
                    sat_unsat_split.append([unsat, sat])

                if 0 in negative_gains:
                    # if there's a flip with negative gain of 0, then flip it.
                    flip_index = random.choice(np.where(negative_gains == np.zeros(1))[0])
                    net_gain, literal, clauses = self.perform_zero_damage_flip(flip_index, bc, sat_unsat_split)
                    satisfiability = [True]*net_gain

                else:
                    if self.p >= random.uniform(0.0, 1.0):
                        # select random variable from bc clause and flip it.
                        flip_index = random.sample(range(0, len(bc)), 1)[0]
                        net_gain, literal, clauses, satisfiability = self.perform_flip(flip_index, bc, sat_unsat_split,
                                                                                      evaluation, negative_gains)
                    else:
                        # select random variable w/ minimum negative gain from bc clause and flip it.
                        flip_index = random.choice(np.where(negative_gains == np.min(negative_gains))[0])
                        net_gain, literal, clauses, satisfiability = self.perform_flip(flip_index, bc, sat_unsat_split,
                                                                                      evaluation, negative_gains)
                # update fitness (number of UNSAT clauses):
                self.fitness -= net_gain
                # update dictionary of clauses:
                self.update_dict_clauses(clauses, satisfiability, return_dict=False)
                # update Tabu variables:
                self.update_tabu_list(var=literal, iteration=j)

                if self.fitness == 0: # if the number of UNSAT clauses is 0, then break the loop and return the results.
                    print('All clauses were satisfied.')
                    return self.fitness, self.current_solution, self.total_steps, self.total_restarts

            if self.fitness < self.output_best_unsat: # if the algorithm reached a new minimum number of UNSAT clauses:
                # update the number of UNSAT clauses:
                self.output_best_unsat = self.fitness
                # update the best truth assignment found:
                self.output_best_assignment = self.current_solution
        # this will be executed, if and only if, the algorithm made (max_tries x max_flips) search steps and didn't find a solution.
        print('Warning: Best solution found has {} unsatisfied clauses.'.format(self.output_best_unsat))
        return self.output_best_unsat, self.output_best_assignment, self.total_steps, self.total_restarts


if __name__ == "__main__":
    # do not run the code if there are less than 7 arguments in the terminal:
    if len(sys.argv) < 7:
        print("Error - Incorrect input")
        print("Expecting: python3 WalkSAT.py [instance] [executions] [max_flips] [max_tries] [p] [tl]")
        sys.exit(0)

    problem_file = sys.argv[1]
    executions = int(sys.argv[2])
    max_flips = int(sys.argv[3])
    max_tries = int(sys.argv[4])
    p = float(sys.argv[5])
    tl = int(sys.argv[6])

    # create empty lists to store the results:
    steps = []
    restarts = []
    unsat = []
    cpu_time = []
    for i in range(int(executions)): # run the algorithm for a given number of executions.
        t0 = process_time() # CPU time at start.
        walksat = WalkSAT(max_flips=max_flips, max_tries=max_tries, path_to_file=problem_file, p=p, tl=tl)
        best_unsat, best_assignment, total_steps, total_restarts = walksat.init_search()
        t1 = process_time() # CPU time at end.
        # store results:
        cpu_time.append(t1 - t0)
        unsat.append(best_unsat)
        steps.append(total_steps)
        restarts.append(total_restarts)

    # output file with descriptive statistics:
    with open("solution_{}.txt".format(problem_file), 'w', encoding='utf-8') as f:
        f.write("c Algorithm: {}\n".format(WalkSAT.__name__))
        f.write("c max_flips: {}\n".format(max_flips))
        f.write("c max_tries: {}\n".format(max_tries))
        f.write("c p: {}\n".format(p))
        f.write("c tl: {}\n".format(tl))
        f.write("c Number of Executions: {}\n".format(executions))
        f.write("c Success Rate: {}\n".format((len(unsat) - np.count_nonzero(unsat)) / len(unsat) * 100))
        f.write('c =============================\n')
        if executions == 1: # if the number of executions is 1, the file will also contain a candidate solution.
            for i in np.split(np.array(best_assignment), 2):
                f.write("v {}\n".format(str(i)[1:-1]))
            f.write("v 0\n")

        f.write('c Average flips: {}\n'.format(np.round(np.mean(steps), 3)))
        f.write('c Median flips: {}\n'.format(np.round(np.median(steps), 3)))
        f.write('c Std flips: {}\n'.format(np.round(np.std(steps), 3)))
        f.write('c Variation Coefficient Flips: {}\n'.format(np.round(np.std(steps)/np.mean(steps), 3)))
        f.write('c Max flips: {}\n'.format(np.round(np.max(steps), 3)))
        f.write('c Min flips: {}\n'.format(np.round(np.min(steps), 3)))
        f.write('c ------\n')
        f.write('c Average restarts: {}\n'.format(np.round(np.mean(restarts), 3)))
        f.write('c Median restarts: {}\n'.format(np.round(np.median(restarts), 3)))
        f.write('c Std restarts: {}\n'.format(np.round(np.std(restarts), 3)))
        f.write('c Max flips: {}\n'.format(np.round(np.max(restarts), 3)))
        f.write('c Min flips: {}\n'.format(np.round(np.min(restarts), 3)))
        f.write('c ------\n')
        f.write('c Average CPU time (s): {}\n'.format(np.round(np.mean(cpu_time), 3)))
        f.write('c Median CPU time (s): {}\n'.format(np.round(np.median(cpu_time), 3)))
        f.write('c Std CPU time (s): {}\n'.format(np.round(np.std(cpu_time), 3)))
        f.write('c Variation Coefficient CPU time (s): {}\n'.format(np.round(np.std(cpu_time)/np.mean(cpu_time), 3)))
        f.write('c Max flips: {}\n'.format(np.round(np.max(cpu_time), 3)))
        f.write('c Min flips: {}\n'.format(np.round(np.min(cpu_time), 3)))
