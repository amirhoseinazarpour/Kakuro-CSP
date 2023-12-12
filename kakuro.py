import search
import utils
import random
from collections import defaultdict, Counter
from operator import eq, neg

from sortedcontainers import SortedSet

import search
from utils import argmin_random_tie, count, first, extend
from time import time
from itertools import permutations



kakuro_given4x3 = [
    ['*', '*', '*', [6, ''], [3, '']],
    ['*', [4, ''], [3, 3], '_', '_'],
    [['', 10], '_', '_', '_', '_'],
    [['', 3], '_', '_', '*', '*']
]


kakuro_given5x7 = [
    ['*', [17, ''], [28, ''], '*', [42, ''], [22, '']],
    [['', 9], '_', '_', [31, 14], '_', '_'],
    [['', 20], '_', '_', '_', '_', '_'],
    ['*', ['', 30], '_', '_', '_', '_'],
    ['*', [22, 24], '_', '_', '_', '*'],
    [['', 25], '_', '_', '_', '_', [11, '']],
    [['', 20], '_', '_', '_', '_', '_'],
    [['', 14], '_', '_', ['', 17], '_', '_']
]


kakuro_given14x14 = [
    ['*', '*', '*', '*', '*', [4, ''], [24, ''], [11, ''], '*', '*', '*', [11, ''], [17, ''], '*', '*'],
    ['*', '*', '*', [17, ''], [11, 12], '_', '_', '_', '*', '*', [24, 10], '_', '_', [11, ''], '*'],
    ['*', [4, ''], [16, 26], '_', '_', '_', '_', '_', '*', ['', 20], '_', '_', '_', '_', [16, '']],
    [['', 20], '_', '_', '_', '_', [24, 13], '_', '_', [16, ''], ['', 12], '_', '_', [23, 10], '_', '_'],
    [['', 10], '_', '_', [24, 12], '_', '_', [16, 5], '_', '_', [16, 30], '_', '_', '_', '_', '_'],
    ['*', '*', [3, 26], '_', '_', '_', '_', ['', 12], '_', '_', [4, ''], [16, 14], '_', '_', '*'],
    ['*', ['', 8], '_', '_', ['', 15], '_', '_', [34, 26], '_', '_', '_', '_', '_', '*', '*'],
    ['*', ['', 11], '_', '_', [3, ''], [17, ''], ['', 14], '_', '_', ['', 8], '_', '_', [7, ''], [17, ''], '*'],
    ['*', '*', '*', [23, 10], '_', '_', [3, 9], '_', '_', [4, ''], [23, ''], ['', 13], '_', '_', '*'],
    ['*', '*', [10, 26], '_', '_', '_', '_', '_', ['', 7], '_', '_', [30, 9], '_', '_', '*'],
    ['*', [17, 11], '_', '_', [11, ''], [24, 8], '_', '_', [11, 21], '_', '_', '_', '_', [16, ''], [17, '']],
    [['', 29], '_', '_', '_', '_', '_', ['', 7], '_', '_', [23, 14], '_', '_', [3, 17], '_', '_'],
    [['', 10], '_', '_', [3, 10], '_', '_', '*', ['', 8], '_', '_', [4, 25], '_', '_', '_', '_'],
    ['*', ['', 16], '_', '_', '_', '_', '*', ['', 23], '_', '_', '_', '_', '_', '*', '*'],
    ['*', '*', ['', 6], '_', '_', '*', '*', ['', 15], '_', '_', '_', '*', '*', '*', '*']
]


kakuro_intermediate6x6 = [
    ['*', [11, ''], [16, ''], [30, ''], '*', [24, ''], [11, '']],
    [['', 24], '_', '_', '_', ['', 9], '_', '_'],
    [['', 16], '_', '_', '_', [14, 17], '_', '_'],
    ['*', '*', [22, 20], '_', '_', '_', '*'],
    ['*', [3, 24], '_', '_', '_', [10, ''], [13, '']],
    [['', 7], '_', '_', ['', 19], '_', '_', '_'],
    [['', 11], '_', '_', ['', 7], '_', '_', '_']
]


kakuro_hard8x8 = [
    ['*', [28, ''], [15, ''], '*', [9, ''], [15, ''], '*', [9, ''], [12, '']],
    [['', 10], '_', '_', [15, 6], '_', '_', [10, 4], '_', '_'],
    [['', 38], '_', '_', '_', '_', '_', '_', '_', '_'],
    [['', 17], '_', '_', '_', ['', 4], '_', '_', [27, ''], '*'],
    [['', 13], '_', '_', [7, ''], [17, 19], '_', '_', '_', [15, '']],
    ['*', ['', 8], '_', '_', '_', '*', [16, 3], '_', '_'],
    ['*', [11, ''], [4, 4], '_', '_', [3, 24], '_', '_', '_'],
    [['', 44], '_', '_', '_', '_', '_', '_', '_', '_'],
    [['', 3], '_', '_', ['', 6], '_', '_', ['', 10], '_', '_']
]
class CSP(search.Problem):

    def __init__(self, variables, domains, neighbors, constraints):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        super().__init__(())
        variables = variables or list(domains.keys())
        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.curr_domains = None
        self.nassigns = 0

    def assign(self, var, val, assignment):
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):

        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):


        def conflict(var2):
            return var2 in assignment and not self.constraints(var, val, var2, assignment[var2])

        return count(conflict(v) for v in self.neighbors[var])

    def display(self, assignment):

        print(assignment)



    def actions(self, state):

        if len(state) == len(self.variables):
            return []
        else:
            assignment = dict(state)
            var = first([v for v in self.variables if v not in assignment])
            return [(var, val) for val in self.domains[var]
                    if self.nconflicts(var, val, assignment) == 0]

    def result(self, state, action):

        (var, val) = action
        return state + ((var, val),)

    def goal_test(self, state):

        assignment = dict(state)
        return (len(assignment) == len(self.variables)
                and all(self.nconflicts(variables, assignment[variables], assignment) == 0
                        for variables in self.variables))



    def support_pruning(self):

        if self.curr_domains is None:
            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    def suppose(self, var, value):

        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):

        self.curr_domains[var].remove(value)
        if removals is not None:
            removals.append((var, value))

    def choices(self, var):

        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):

        self.support_pruning()
        return {v: self.curr_domains[v][0]
                for v in self.variables if 1 == len(self.curr_domains[v])}

    def restore(self, removals):

        for B, b in removals:
            self.curr_domains[B].append(b)

    # This is for min_conflicts search

    def conflicted_vars(self, current):

        return [var for var in self.variables
                if self.nconflicts(var, current[var], current) > 0]




def no_arc_heuristic(csp, queue):
    return queue


def dom_j_up(csp, queue):
    return SortedSet(queue, key=lambda t: neg(len(csp.curr_domains[t[1]])))


def AC3(csp, queue=None, removals=None, arc_heuristic=dom_j_up):

    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        revised, checks = revise(csp, Xi, Xj, removals, checks)
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
    return True, checks

def revise(csp, Xi, Xj, removals, checks=0):
    revised = False
    for x in csp.curr_domains[Xi][:]:

        conflict = True
        for y in csp.curr_domains[Xj]:
            if csp.constraints(Xi, x, Xj, y):
                conflict = False
            checks += 1
            if not conflict:
                break
        if conflict:
            csp.prune(Xi, x, removals)
            revised = True
    return revised, checks




def AC3b(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()

        Si_p, Sj_p, Sj_u, checks = partition(csp, Xi, Xj, checks)
        if not Si_p:
            return False, checks
        revised = False
        for x in set(csp.curr_domains[Xi]) - Si_p:
            csp.prune(Xi, x, removals)
            revised = True
        if revised:
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
        if (Xj, Xi) in queue:
            if isinstance(queue, set):

                queue.difference_update({(Xj, Xi)})
            else:
                queue.difference_update((Xj, Xi))

            for vj_p in Sj_u:
                for vi_p in Si_p:
                    conflict = True
                    if csp.constraints(Xj, vj_p, Xi, vi_p):
                        conflict = False
                        Sj_p.add(vj_p)
                    checks += 1
                    if not conflict:
                        break
            revised = False
            for x in set(csp.curr_domains[Xj]) - Sj_p:
                csp.prune(Xj, x, removals)
                revised = True
            if revised:
                for Xk in csp.neighbors[Xj]:
                    if Xk != Xi:
                        queue.add((Xk, Xj))
    return True, checks


def partition(csp, Xi, Xj, checks=0):
    Si_p = set()
    Sj_p = set()
    Sj_u = set(csp.curr_domains[Xj])
    for vi_u in csp.curr_domains[Xi]:
        conflict = True

        for vj_u in Sj_u - Sj_p:

            if csp.constraints(Xi, vi_u, Xj, vj_u):
                conflict = False
                Si_p.add(vi_u)
                Sj_p.add(vj_u)
            checks += 1
            if not conflict:
                break

        if conflict:
            for vj_p in Sj_p:

                if csp.constraints(Xi, vi_u, Xj, vj_p):
                    conflict = False
                    Si_p.add(vi_u)
                checks += 1
                if not conflict:
                    break
    return Si_p, Sj_p, Sj_u - Sj_p, checks



def first_unassigned_variable(assignment, csp):

    return first([var for var in csp.variables if var not in assignment])


def mrv(assignment, csp):

    return argmin_random_tie([v for v in csp.variables if v not in assignment],
                             key=lambda var: num_legal_values(csp, var, assignment))


def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0 for val in csp.domains[var])





def unordered_domain_values(var, assignment, csp):

    return csp.choices(var)


def lcv(var, assignment, csp):

    return sorted(csp.choices(var), key=lambda val: csp.nconflicts(var, val, assignment))





def no_inference(csp, var, value, assignment, removals):
    return True


def forward_checking(csp, var, value, assignment, removals):

    csp.support_pruning()
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:
                return False
    return True



def mac(csp, var, value, assignment, removals, constraint_propagation=AC3b):

    return constraint_propagation(csp, {(X, var) for X in csp.neighbors[var]}, removals)





def backtracking_search(csp, select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values, inference=no_inference):


    def backtrack(assignment):
        if len(assignment) == len(csp.variables):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None

    result = backtrack({})
    assert result is None or csp.goal_test(result)
    return result



def min_conflicts(csp, max_steps=100000):

    csp.current = current = {}
    for var in csp.variables:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)

    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            return current
        var = random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    return None


def min_conflicts_value(csp, var, current):

    return argmin_random_tie(csp.domains[var], key=lambda val: csp.nconflicts(var, val, current))



class Kakuro(CSP):


    def __init__(self, kakuro_puzzle):
        variables = []

        domains = {}

        neighbors = {}

        self.puzzle = kakuro_puzzle

        for i in range(len(kakuro_puzzle)):
            for j in range(len(kakuro_puzzle[i])):

                if kakuro_puzzle[i][j] == "_":
                    var = "X" + str(i) + "," + str(j)
                    variables.append(var)

                    domains[var] = list(map(str, list(range(1, 10))))

                if kakuro_puzzle[i][j] != '_' and kakuro_puzzle[i][j] != '*':


                    if kakuro_puzzle[i][j][0] != "":
                        hidden_var = "C_d" + str(i) + "," + str(j)
                        variables.append(hidden_var)

                        cell_counter = 0
                        for m in range(i + 1, len(kakuro_puzzle)):
                            if kakuro_puzzle[m][j] != "_":
                                break

                            nei = "X" + str(m) + "," + str(j)

                            if hidden_var not in neighbors:
                                neighbors[hidden_var] = []
                            neighbors[hidden_var].append(nei)

                            if nei not in neighbors:
                                neighbors[nei] = []
                            neighbors[nei].append(hidden_var)

                            cell_counter += 1

                        perms = list(map("".join, permutations('123456789', cell_counter)))
                        domains[hidden_var] = [perm for perm in perms if
                                               sum(int(x) for x in perm) == kakuro_puzzle[i][j][0]]


                    if kakuro_puzzle[i][j][1] != "":
                        hidden_var = "C_r" + str(i) + "," + str(j)
                        variables.append(hidden_var)

                        cell_counter = 0
                        for k in range(j + 1, len(kakuro_puzzle[i])):
                            if kakuro_puzzle[i][k] != "_":
                                break

                            nei = "X" + str(i) + "," + str(k)

                            if hidden_var not in neighbors:
                                neighbors[hidden_var] = []
                            neighbors[hidden_var].append(nei)

                            if nei not in neighbors:
                                neighbors[nei] = []
                            neighbors[nei].append(hidden_var)

                            cell_counter += 1

                        perms = list(map("".join, permutations('123456789', cell_counter)))
                        domains[hidden_var] = [perm for perm in perms if
                                               sum(int(x) for x in perm) == kakuro_puzzle[i][j][1]]

        CSP.__init__(self, variables, domains, neighbors, self.kakuro_constraint)



    def kakuro_constraint(self, A, a, B, b):
        if A[0] == "X" and B[0] == "C":
            X_i = int(A[1: A.index(",")])
            X_j = int(A[A.index(",") + 1:])

            C_i = int(B[3: B.index(",")])
            C_j = int(B[B.index(",") + 1:])

            if B[2] == "d":
                ind = X_i - C_i - 1
                hidden_var = "C_d" + str(C_i) + "," + str(C_j)

                if b[ind] == a:
                    return True

            else:
                ind = X_j - C_j - 1
                hidden_var = "C_r" + str(C_i) + "," + str(C_j)

                if b[ind] == a:
                    return True

        elif A[0] == "C" and B[0] == "X":
            C_i = int(A[3: A.index(",")])
            C_j = int(A[A.index(",") + 1:])

            X_i = int(B[1: B.index(",")])
            X_j = int(B[B.index(",") + 1:])

            if A[2] == "d":
                ind = X_i - C_i - 1
                hidden_var = "C_d" + str(C_i) + "," + str(C_j)

                if a[ind] == b:
                    return True

            else:  # A[2] == "r":
                ind = X_j - C_j - 1
                hidden_var = "C_r" + str(C_i) + "," + str(C_j)

                if a[ind] == b:
                    return True

        return False

    def display(self, assignment=None):
        for i in range(len(self.puzzle)):
            line = ""
            for j in range(len(self.puzzle[i])):
                if self.puzzle[i][j] == '*':
                    line += " * \t"
                elif self.puzzle[i][j] == "_":
                    var = "X" + str(i) + "," + str(j)
                    if assignment != None:
                        if var in assignment:
                            line += " " + assignment[var] + " \t"
                        else:
                            line += " _ \t"
                    else:
                        line += " _ \t"
                else:
                    sum1 = str(self.puzzle[i][j][0]) if self.puzzle[i][j][0] else " "
                    sum2 = str(self.puzzle[i][j][1]) if self.puzzle[i][j][1] else " "
                    line += sum1 + "\\" + sum2 + "\t"
            print(line)
            print()




Kakuro_problem = Kakuro(kakuro_given5x7)

assignments = backtracking_search(Kakuro_problem, select_unassigned_variable=mrv, inference=forward_checking)

Kakuro_problem.display(assignments)

