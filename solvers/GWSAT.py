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

class GWSAT:
    def __init__(self, max_flips, max_tries, path_to_file, wp):
        """
        Initialize parameters and load CFN.
        """
        self.max_tries = max_tries
        self.max_flips = max_flips
        self.path_to_file = path_to_file
        self.wp = wp
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
        self.cnf, self.variables = load_cnf(instance=cnf_instance)

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
        if return_dict: # this is optional in case further pre-processing is required.
            return self.clau_dict
        else:
            pass

    def get_usat_clauses(self):
        """ Filter a dictionary by value and get keys.

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

    def select_flip_gsat_step(self, improvement, clauses, evaluation):
        """ Given a list of net gains, select the index of the variable with highest gain.
        Ties are broken randomly: if there are two gains with the same value, random.choice will
        select one. If there's a single maximum gain, random.choice will always pick this one.
        This function also flips the variable in the current solution.

        :param improvement: A list of net gains that would result after a GSAT step.
        :param clauses: A list of clauses where each of the variables are in.
        :param evaluation: A list boolean values indicating which clauses would be SAT/UNSAT after flipping a variable.
        :return: 1) The net gain after flipping a variable, 2) the clauses where the variable is in, and
        3) a list of boolean values indicating if the clauses became SAT or UNSAT.
        """
        flip_index = random.choice(np.where(improvement == np.max(improvement))[0])
        # flip the variable that minimizes the number of UNSAT clauses.
        self.current_solution[flip_index] = self.current_solution[flip_index] * (-1)
        # get the net gain after flipping the selected variable.
        net_gain = improvement[flip_index]

        return net_gain, clauses[flip_index], evaluation[flip_index]


    def select_flip_random_step(self):
        """
        Perform a Random Walk step from a given array of variables involved in at least one unsatisfied clause.
        1. Get of UNSAT clauses with literals.
        2. Extract literals from UNSAT clauses and convert them to unique variables.
        3. Randomly choose one variable, flip it and compute the net gain and flip index.

        :return: 1) The net gain after flipping a variable, 2) the clauses where the variable is in, and
        3) a list of boolean values indicating if the clauses became SAT or UNSAT.
        """
        # select UNSAT clauses.
        unsat_clauses = self.get_usat_clauses()
        # extract literals from clauses.
        vars = reduce(lambda x, y: x + y, unsat_clauses)
        # convert literals to variables and create an array of unique variables in UNSAT clauses.
        candidate_vars = np.unique(np.abs(vars))
        # randomly choose a variable.
        random_sel = random.choice(candidate_vars) - 1
        # find variable in candidate solution and store its assignment.
        variable = self.current_solution[random_sel]
        # flip variable.
        self.current_solution[random_sel] = variable * (-1)
        # check current UNSAT clauses only in the subset of clauses where the variable is in.
        sat, unsat = self.split_sat_unsat(self.var_dict[abs(variable)])
        current_unsat = len(unsat)
        # compute the number of SAT clauses where the variable is in that would be
        # UNSAT if I flip the variable (we only check this for SAT clauses where the variable is in).
        potential_unsat, bool_list = SAT(self.current_solution, sat, return_clauses=True)

        # create a list of boolean values that indicates which clauses, where the variable is in, would
        # become SAT or UNSAT after flipping it. We know that all the current UNSAT clauses will be SAT,
        # so we can just do: ([True] * len(unsat)) instead of checking it.
        eval = ([True] * len(unsat)) + bool_list
        affected_clauses = unsat + sat

        # calculate net gain.
        # B0 = number of current UNSAT clauses.
        # B1 = number of UNSAT clause after flipping the variable.
        # net gain = B0 - B1.
        net_gain = current_unsat - potential_unsat

        return net_gain, affected_clauses, eval


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
            self.current_solution = random_assignment  # which becomes the current solution to the problem.
            # then, calculate the number of UNSAT clauses using the current solution and return these clauses.
            self.fitness, unsat_clauses = SAT(random_assignment, self.cnf, return_clauses=True)

            # fill the dictionaries that contribute to make an efficient implementation of the algorithm:
            self.var_dict = self.generate_dict_variables()
            self.clau_dict = self.generate_dict_clauses(unsat_bool_list=unsat_clauses)

            # if the random candidate solution is a solution to the problem then break the loop.
            if self.fitness == 0:
                print('All clauses were satisfied after {} tries'.format(i))
                return self.fitness, self.current_solution, self.total_steps, self.total_restarts

            for j in range(self.max_flips):
                self.total_steps += 1 # search steps counter
                # create empty lists to store useful data.
                improvement = []
                clauses = []
                evaluation = []
                if self.wp <= random.uniform(0.0, 1.0):
                    for f in range(0, self.variables): # the algorithm goes through each variable.
                        # make of copy of the current solution.
                        candidate_solution = self.current_solution.copy()
                        # simulate a flip
                        variable = candidate_solution[f]
                        candidate_solution[f] = variable * (-1)
                        # get the split between SAT and UNSAT clauses where the variable is in
                        # using the dictionary of clauses and boolean values.
                        sat, unsat = self.split_sat_unsat(self.var_dict[abs(variable)])
                        current_unsat = len(unsat)
                        # compute the number of SAT clauses where the variable is in that would be
                        # UNSAT if I flip the variable (we only check this for SAT clauses where the variable is in).
                        potential_unsat, bool_list = SAT(candidate_solution, sat, return_clauses=True)

                        # create a list of boolean values that indicates which clauses, where the variable is in, would
                        # become SAT or UNSAT after flipping it. We know that all the current UNSAT clauses will be SAT,
                        # so we can just do: ([True] * len(unsat)) instead of checking it.
                        eval = ([True] * len(unsat)) + bool_list
                        affected_clauses = unsat + sat

                        # store the results:
                        clauses.append(affected_clauses)
                        evaluation.append(eval)
                        # append net gain as (current_unsat: B0) - (potential_unsat: B1).
                        improvement.append(current_unsat - potential_unsat)

                    # to perform a GSAT step, the algorithm selects the index of the flip that maximizes the net gain:
                    net_gain, clause, satisfiability = self.select_flip_gsat_step(improvement, clauses, evaluation)

                else: # with probability wp perform a Random Walk step:
                    net_gain, clause, satisfiability = self.select_flip_random_step()

                # update fitness (number of UNSAT clauses):
                self.fitness -= net_gain
                # update dictionary of clauses.
                self.update_dict_clauses(clause, satisfiability, return_dict=False)

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
    # do not run the code if there are less than 6 arguments in the terminal:
    if len(sys.argv) < 6:
        print("Error - Incorrect input")
        print("Expecting: python3 GWSAT.py [instance] [executions] [max_flips] [max_tries] [wp]")
        sys.exit(0)

    problem_file = sys.argv[1]
    executions = int(sys.argv[2])
    max_flips = int(sys.argv[3])
    max_tries = int(sys.argv[4])
    wp = float(sys.argv[5])

    # create empty lists to store the results:
    steps = []
    restarts = []
    unsat = []
    cpu_time = []
    for i in range(int(executions)):  # run the algorithm for a given number of executions.
        t0 = process_time() # CPU time at start.
        gwsat_algo = GWSAT(max_flips=max_flips, max_tries=max_tries, path_to_file=problem_file, wp=wp)
        best_unsat, best_assignment, total_steps, total_restarts = gwsat_algo.init_search()
        t1 = process_time() # CPU time at end.
        # store results:
        cpu_time.append(t1 - t0)
        unsat.append(best_unsat)
        steps.append(total_steps)
        restarts.append(total_restarts)

    # output file with descriptive statistics:
    with open("solution_{}.txt".format(problem_file), 'w', encoding='utf-8') as f:
        f.write("c Algorithm: {}\n".format(GWSAT.__name__))
        f.write("c max_flips: {}\n".format(max_flips))
        f.write("c max_tries: {}\n".format(max_tries))
        f.write("c wp: {}\n".format(wp))
        f.write("c Number of Executions: {}\n".format(executions))
        f.write("c Success Rate: {}\n".format((len(unsat) - np.count_nonzero(unsat)) / len(unsat) * 100))
        f.write('c =============================\n')
        if executions == 1:
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
