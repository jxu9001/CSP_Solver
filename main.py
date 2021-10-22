# Jerry Xu
# CS 4365 Spring 2021 Homework 2 Part 2
# I used the following command to run the solver:
# python3 <filename> <path_to_var> <path_to_con> <con_procedure>

import itertools
import operator
from copy import deepcopy
import sys

# dictionary that allows for conversion of "op" strings to actual operators
operators = {
    ">": operator.gt,
    "<": operator.lt,
    "=": operator.eq,
    "!": operator.ne
}


# Variable class w/ 2 attributes
# domain: list of ints e.g. [1, 2, 3, 4]
# value: int
class Variable:
    def __init__(self):
        self.domain = None
        self.value = None

    def set_domain(self, domain):
        self.domain = domain

    def set_value(self, value):
        self.value = value

    def get_domain(self):
        return self.domain

    def get_value(self):
        return self.value


def main():
    # initialize the line number
    global line_number
    line_number = 0

    # initialize needed data structures
    variables, constraints, assignment = {}, [], {}

    # command line args
    var_file_name, con_file_name, fc_procedure = sys.argv[1], sys.argv[2], sys.argv[3]

    # read .var file into a dictionary where key = variable's name and v = Variable object
    with open(var_file_name) as var_file:
        for line in var_file:
            line = line.strip().replace(":", "").split()
            # create a Variable object and add it to the variables dictionary
            variable = Variable()
            variable.set_domain([int(val) for val in line[1:]])
            variable.set_value(None)
            variables[line[0]] = variable

    # read .con file into a list of lists where each sublist is a constraint in the form ['v1', 'op', 'v2']
    with open(con_file_name) as con_file:
        for line in con_file:
            constraints.append(line.split())

    # check which consistency enforcing procedure to use
    if fc_procedure == "none":
        forward_checking = False
    else:
        forward_checking = True

    result = backtracking(assignment, variables, constraints, forward_checking)

    # check if CSP actually has a solution
    if result:
        print_solution(result)


def backtracking(assignment, variables, constraints, forward_checking):
    """
    recursive backtracking algorithm found in the lecture slides
    """
    # assignment is a dictionary where k = variable's name and v = variable's value
    # check if assignment is complete
    complete = True
    for var in variables.values():
        if var.get_value() is None:
            complete = False
    if complete:
        return assignment

    # select variable and get its domain, ordered according to the LCV heuristic
    var = select_unassigned_variable(variables, constraints)
    ordered_domain = order_domain_values(variables, constraints, var)

    for val in ordered_domain:
        consistent = True
        # check if each value in the ordered domain is consistent with the assignment
        for con in constraints:
            # constraints are in the form ['v1', 'op', 'v2']
            v1, op, v2 = con[0], operators[con[1]], con[2]
            # check if selected variable is on LHS or RHS of constraint
            # also check if var on other side of constraint has a value
            if var == v1 and variables[v2].get_value() is not None:
                consistent = op(val, variables[v2].get_value())
            elif var == v2 and variables[v1].get_value() is not None:
                consistent = op(variables[v1].get_value(), val)
            if not consistent:
                print_branch(assignment, var, val, forward_checking)
                # don't need to check any more constraints
                break

        if consistent:
            # add val to assignment
            variables[var].set_value(val)
            assignment[var] = val
            # forward checking
            if forward_checking:
                # run forward checking, deepcopy is used so we pass by value instead of reference
                res_variables = run_forward_checking(deepcopy(variables), constraints, var)
                # check if forward checking resulted in an empty domain
                for variable in res_variables.values():
                    if len(variable.get_domain()) == 0:
                        print_branch(assignment, var, val, forward_checking)
            else:
                res_variables = variables

            result = backtracking(assignment, res_variables, constraints, forward_checking)
            if result:
                return result

            # remove val from assignment
            variables[var].set_value(None)
            assignment.pop(var)
    return False


def select_unassigned_variable(variables, constraints):
    """
    chooses a variable using the most constrained variable heuristic,
    breaking ties using the most constraining variable heuristic,
    and then alphabetically
    """
    # initialize most constrained variable
    mcv = None
    for var in variables:
        # check if the variable has been assigned a value
        if variables[var].get_value() is None:
            # set mcv to the first var seen
            if mcv is None:
                mcv = var
            # set mcv to current var if curr var is more constrained
            if len(variables[var].get_domain()) < len(variables[mcv].get_domain()):
                mcv = var
            # if two variables are equally constrained then apply the most constraining variable heuristic
            elif len(variables[var].get_domain()) == len(variables[mcv].get_domain()):
                # number of constraints on the most constrained variable seen so far
                max_count = 0
                # number of constraints on the current variable
                curr_count = 0
                for con in constraints:
                    # constraints are in the form ['v1', 'op', 'v2']
                    v1, v2 = con[0], con[2]
                    # check if mcv/current var is on LHS or RHS of constraint
                    # also ignore already assigned variables
                    mcv_on_lhs = v1 == mcv and variables[v2].get_value() is None
                    mcv_on_rhs = v2 == mcv and variables[v1].get_value() is None
                    var_on_lhs = v1 == var and variables[v2].get_value() is None
                    var_on_rhs = v2 == var and variables[v1].get_value() is None
                    if mcv_on_lhs or mcv_on_rhs:
                        max_count += 1
                    if var_on_lhs or var_on_rhs:
                        curr_count += 1
                # the '>' ensures that ties are broken alphabetically
                # e.g. if A and F are both equally constrained then curr_count !> max_count and the mcv is not set to F
                if curr_count > max_count:
                    mcv = var
    return mcv


def order_domain_values(variables, constraints, var):
    """
    given a variable, return an array of values to try ordered by the LCV heuristic,
    breaking ties by preferring smaller values
    """
    # dictionary where k = num. legal values remaining in neighboring unassigned variables of var (int)
    # v = value(s) of var s.t. var has k values remaining (list)
    constraining_values = {}
    # check all possible values of the given var
    for val_1 in variables[var].get_domain():
        # initialize count of legal vals
        num_legal_values = 0
        # given a constraint and a var,
        # find the # of legal vals remaining in neighboring unassigned variables
        for con in constraints:
            # constraints are in the form ['v1', 'op', 'v2']
            v1, op, v2 = con[0], operators[con[1]], con[2]

            # variable we want the possible values of is on LHS of constraint
            if var == v1 and variables[v2].get_value() is None:
                for val_2 in variables[v2].get_domain():
                    if op(val_1, val_2):
                        num_legal_values += 1

            # variable we want the possible values of is on RHS of constraint
            elif var == v2 and variables[v1].get_value() is None:
                for val_2 in variables[v1].get_domain():
                    if op(val_2, val_1):
                        num_legal_values += 1

        # 2+ values of var w/ the same # of legal values in neighboring unassigned variables
        if num_legal_values in constraining_values:
            constraining_values[num_legal_values].append(val_1)
        # only 1 value of var w/ the same # of legal values in neighboring unassigned variables
        else:
            constraining_values[num_legal_values] = [val_1]

    ordered_domain_values = []

    # sort keys (num. legal vals remaining for given var) in descending order
    # we want var w/ max # of legal vals in neighboring unassigned variables
    for key in sorted(constraining_values.keys(), reverse=True):
        ordered_domain_values.append(constraining_values[key])

    # flatten the list of keys
    return list(itertools.chain(*ordered_domain_values))


def run_forward_checking(variables, constraints, var):
    """
    implements forward checking
    """
    for con in constraints:
        # list of values to remove from the domain during forward checking
        values_to_remove = []
        # constraints are in the form ['v1', 'op', 'v2']
        v1, op, v2 = con[0], operators[con[1]], con[2]

        # variable we want to run forward checking on is on LHS of constraint
        if var == v1 and variables[v2].get_value() is None:
            # check all possible values of var on RHS of constraint
            for val in variables[v2].get_domain():
                # if value violates constraint add it to the list of values to remove
                if not op(variables[var].get_value(), val):
                    values_to_remove.append(val)
            # remove those values from the variable's domain
            for v in values_to_remove:
                variables[v2].get_domain().remove(v)

        # variable we want to run forward checking on is on RHS of constraint
        elif var == v2 and variables[v1].get_value() is None:
            # check all possible values of var on LHS of constraint
            for val in variables[v1].get_domain():
                # if value violates constraint add it to the list of values to remove
                if not op(val, variables[var].get_value()):
                    values_to_remove.append(val)
            # remove those values from the variable's domain
            for v in values_to_remove:
                variables[v1].get_domain().remove(v)

    return variables


def print_branch(assignment, var, val, forward_checking):
    """
    prints a branch of the search tree
    """
    # an assignment only has consistent values in it
    # e.g. if the branch is A=2, C=1, F=3, D=1 failure
    # only A=2, C=1, F=3 are in the assignment
    global line_number
    count = 1
    line_number += 1
    branch = str(line_number) + ". "
    for v in assignment:
        if forward_checking:
            # end of branch
            if count == len(assignment):
                branch += var + "=" + str(val) + "  failure"
            else:
                branch += v + "=" + str(assignment[v]) + ", "
        else:
            branch += v + "=" + str(assignment[v]) + ", "
            # end of branch
            if count == len(assignment):
                branch += var + "=" + str(val) + "  failure"
        count += 1
    print(branch)


def print_solution(assignment):
    """
    prints the solution
    """
    global line_number
    count = 1
    line_number += 1
    solution = str(line_number) + ". "
    for v in assignment:
        # end of solution
        if count == len(assignment):
            solution += v + "=" + str(assignment[v]) + "  solution"
        else:
            solution += v + "=" + str(assignment[v]) + ", "
        count += 1
    print(solution)


if __name__ == "__main__":
    main()
