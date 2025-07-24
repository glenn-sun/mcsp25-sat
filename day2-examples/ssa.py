# Warning: This file contains syntax not included in 
# standard Python. It will not run.

def division(x, y):
    r = x
    q = 0
    while r >= y:
        r = r - y
        q = q + 1

    assert x == y * q + r
    assert 0 <= r and r < abs(y)

    return (q, r)

# "assume P" means that all future assertions of the form
# "assert Q" should be interpreted as "assert Q or not P".
def unroll2_division(x, y):
    r = x
    q = 0
    if r >= y:
        r = r - y
        q = q + 1
    if r >= y:
        r = r - y
        q = q + 1
    assume r < y

    assert x == y * q + r
    assert 0 <= r and r < abs(y)
    return (q, r)

# "ite" is a primitive expression, just like + or >=. It 
# means "if-then-else".
def ssa_division(x, y):
    r1 = x
    q1 = 0
    b1 = r1 >= y
    r2 = r1 - y
    q2 = q1 + 1
    r3 = ite(b1, r2, r1)
    q3 = ite(b1, q2, q1)
    b2 = r3 >= y
    r4 = r3 - y
    q4 = q3 + 1
    r5 = ite(b2, r4, r3)
    q5 = ite(b2, q4, q3)
    assume r5 < y

    temp1 = y * q5
    temp2 = temp1 + r5
    abs_y = abs(y)
    assert x == temp2
    assert 0 <= r5
    assert r5 < abs_y
    return (q5, r5)