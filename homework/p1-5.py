# Problem 1.5
# Implement your solution to the n-queens puzzle from Problem 1.2.

# The Z3 solver
from z3 import *

# Allows you to loop over all k-element subsets of a list
from itertools import combinations

# Prints a 2D array prettily
from pprint import pprint

# Input:   the size of the board N
# Output:  a list of Z3 constraints
def n_queens_constraints(N):
    #
    # YOUR CODE HERE
    #
    pass

# Input:   a Z3 solution, which you can get the value a Z3 
#          variable X using the syntax model[X]
# Output:  a 2D array of size N x N, where each cell is 
#          either 0 (empty) or 1 (occupied by a queen)
def model_to_board(model, N):
    #
    # YOUR CODE HERE
    #
    pass

if __name__ == "__main__":
    N = 9
    constraints = n_queens_constraints(N)
    s = z3.Solver()
    s.add(*constraints)
    if s.check() == sat:
        model = s.model()
        pprint(model_to_board(model))
    else:
        print("No solution")

    print("Completed in " + str(s.statistics().get_key_value("time")) + " seconds")