from z3 import *
from itertools import combinations

class Node:
    def __init__(self, name, N):
        self.name = name
        self.positions = [Bool(str(name) + "_in_pos_%d" % i) for i in range(N)]
    
    def in_pos(self, i):
        return self.positions[i]

node_names = range(50)

N = len(node_names)
nodes = {name: Node(name, N) for name in node_names}

edge_names = []

from random import random
for (name1, name2) in combinations(node_names, 2):
    if random() < 0.1:
        edge_names.append((name1, name2))
        edge_names.append((name2, name1))

constraints = []

# Each node appears at least once
for name in node_names:
    constraints.append(Or([nodes[name].in_pos(i) for i in range(N)]))

# Each node appears at most once
for name in node_names:
    for i1, i2 in combinations(range(N), 2):
        constraints.append(~(nodes[name].in_pos(i1) & nodes[name].in_pos(i2)))

# Every position has at least one node
for i in range(N):
    constraints.append(Or([nodes[name].in_pos(i) for name in node_names]))

# Every position has at most one node
for i in range(N):
    for name1, name2 in combinations(node_names, 2):
        constraints.append(~(nodes[name1].in_pos(i) & nodes[name2].in_pos(i)))

# Every nonedge pair cannot be adjacent on the path
for (name1, name2) in combinations(node_names, 2):
    if (name1, name2) not in edge_names:
        for i in range(N-1):
            constraints.append(~(nodes[name1].in_pos(i) & nodes[name2].in_pos(i+1)))
            constraints.append(~(nodes[name1].in_pos(i+1) & nodes[name2].in_pos(i)))

def model_to_path(model):
    path = []
    for i in range(N):
        for name in node_names:
            if model[nodes[name].in_pos(i)]:
                path.append(name)
    return path

print(str(len(constraints)) + " constraints listed using " + str(len(node_names) ** 2) + " variables")

s = Solver()
s.add(*constraints)

print("Model created")

if s.check() == sat:
    model = s.model()
    print(model_to_path(model))
else:
    print("No solution")

print("Completed in " + str(s.statistics().get_key_value("time")) + " seconds")