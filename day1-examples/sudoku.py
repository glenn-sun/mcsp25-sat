from z3 import *
from itertools import combinations
from pprint import pprint

class Cell:
    def __init__(self, x, y):
        self.x = x
        self.y = y
        self.options = [Bool("cell_%d_%d_%d" % (x+1, y+1, i+1)) for i in range(9)]

    def has(self, i):
        return self.options[i]

cell = [[Cell(x, y) for x in range(9)] for y in range(9)]

constraints = []

# Every cell has at least one value
for x in range(9):
    for y in range(9):
        constraints.append(Or(cell[x][y].options))

# Every cell has at most one value
for x in range(9):
    for y in range(9):
        for (i1, i2) in combinations(range(9), 2):
            constraints.append(~(cell[x][y].has(i1) & cell[x][y].has(i2)))

# Every row has at least one of each value
for y in range(9):
    for i in range(9):
        constraints.append(Or([cell[x][y].has(i) for x in range(9)]))

# Every row has at most one of each value
for y in range(9):
    for i in range(9):
        for x1, x2 in combinations(range(9), 2):
            constraints.append(~(cell[x1][y].has(i) & cell[x2][y].has(i)))

# Every column has at least one of each value
for x in range(9):
    for i in range(9):
        constraints.append(Or([cell[x][y].has(i) for y in range(9)]))

# Every column has at most one of each value
for x in range(9):
    for i in range(9):
        for (y1, y2) in combinations(range(9), 2):
            constraints.append(~(cell[x][y1].has(i) & cell[x][y2].has(i)))   

boxes = [[(i, j) for i in range(3*x, 3*(x+1)) for j in range(3*y, 3*(y+1))] for x in range(3) for y in range(3)]
# Every 3x3 box has at least one of each value
for box in boxes:
    for i in range(9):
        constraints.append(Or([cell[x][y].has(i) for (x, y) in box]))

# Every 3x3 box has at most one of each value
for box in boxes:
    for i in range(9):
        for (x1, y1), (x2, y2) in combinations(box, 2):
            constraints.append(~(cell[x1][y1].has(i) & cell[x2][y2].has(i)))

nikitas_nemesis = [
    [0, 1, 0, 8, 0, 4, 9, 0, 2],
    [0, 0, 7, 0, 0, 0, 6, 0, 0],
    [0, 4, 0, 2, 7, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 9, 0, 5, 8],
    [0, 0, 9, 0, 0, 0, 1, 0, 0],
    [2, 7, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 3, 2, 0, 9, 0],
    [0, 0, 2, 0, 0, 0, 5, 0, 0],
    [4, 0, 6, 5, 0, 7, 0, 3, 0]
]

def board_to_constraints(board):
    ret = []
    for x in range(9):
        for y in range(9):
            if board[x][y] != 0:
                ret.append(cell[x][y].has(board[x][y]-1))
    return ret

print(len(constraints))

constraints += board_to_constraints(nikitas_nemesis)

def model_to_board(model):
    board = [[0 for x in range(9)] for y in range(9)]
    for x in range(9):
        for y in range(9):
            for i in range(9):
                if model[cell[x][y].has(i)]:
                    board[x][y] = i+1
    return board

print(str(len(constraints)) + " constraints listed using 729 variables")

s = Solver()
s.add(*constraints)

print("Model created")

if s.check() == sat:
    model = s.model()
    pprint(model_to_board(model))
else:
    print("No solution")

print("Completed in " + str(s.statistics().get_key_value("time")) + " seconds")