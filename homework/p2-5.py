# Problem 2.5
# Find a counterexample to the SSA division example.

from z3 import *

x, y, r1, q1, r2, q2, r3, q3, r4, q4, r5, q5, temp1, temp2, abs_y = Ints("x y r1 q1 r2 q2 r3 q3 r4 q4 r5 q5 temp1 temp2 abs_y")
b1, b2 = Bools("b1 b2")

def get_constraints():
    constraints = []
    # Sample first line
    constraints.append(r1 == x)

    #
    # YOUR CODE HERE
    # 
    # Reminders:
    # * The SSA division example is at day2-examples/ssa.py
    # * In Z3, z = ite(b, x, y) is written as z == If(b, x, y)
    # * You will need to use If to define absolute value
    # * Z3 supports all other basic operations you need, like +, >=, etc.
    # * Be careful to use parentheses correctly
    # * Be sure to handle assumptions and assertions correctly
    #
    return constraints

if __name__ == "__main__":
    constraints = get_constraints()
    s = z3.Solver()
    s.add(*constraints)
    if s.check() == sat:
        model = s.model()
        print("Counterexample: x = " + str(model[x]) + ", y = " + str(model[y]))
    else:
        print("Code is correct")

    print("Completed in " + str(s.statistics().get_key_value("time")) + " seconds")