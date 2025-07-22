from z3 import *

A_witch = Bool('A_witch')
B_witch = Bool('B_witch')
C_witch = Bool('C_witch')
D_witch = Bool('D_witch')

A_true = Bool('A_true')
B_true = Bool('B_true')
C_true = Bool('C_true')
D_true = Bool('D_true')

constraints = []

# A: B is a toad. I am not a toad.
constraints.append(A_true == B_witch & ~A_witch)

# B: C is exactly as honest as I am.
constraints.append(B_true == (C_true == B_true))

# C: The number of toads is even. A and I are not both truthtellers. I am not a toad.
even_witches = ~Xor(A_witch, Xor(B_witch, Xor(C_witch, D_witch)))

constraints.append(C_true == (even_witches & ~(A_true & C_true) & ~C_witch))

# D: At least one of the toads is a truthteller. 
constraints.append(D_true == ((A_true & A_witch) | (B_true & B_witch) | (C_true & C_witch) | (D_true & D_witch)))

def model_to_witches_and_truthtellers(model):
    witches = []
    for var in [A_witch, B_witch, C_witch, D_witch]:
        if model[var]:
            witches.append(var.decl().name()[0])
    truthtellers = []
    for var in [A_true, B_true, C_true, D_true]:
        if model[var]:
            truthtellers.append(var.decl().name()[0])
    return witches, truthtellers


s = Solver()
s.add(*constraints)

print("Model created")

if s.check() == sat:
    model = s.model()
    witches, truthtellers = model_to_witches_and_truthtellers(model)
    print("Witches: " + str(witches))
    print("Truthtellers: " + str(truthtellers))
else:
    print("No solution")

print("Completed in " + str(s.statistics().get_key_value("time")) + " seconds")