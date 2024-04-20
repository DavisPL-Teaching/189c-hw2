"""
Part 3: Pigeonhole Principle

This part will explore some of the limitations and performance
of Z3.

A famous problem that solvers like Z3 sometimes have
difficulty with is the pigeonhole principle.
This principle can either take a long time to prove,
or it can return unknown, as we will see.

=== What is the pigeonhole principle? ===

This is a principle that says the following:

"If you have n+1 pigeons and they are in n holes,
then at least one hole has more than one pigeon."

For example, if you put 4 pigeons in 3 holes,
then at least one hole has at least 2 pigeons.

=== Implementation ===

You will be asked to write two functions:

- pigeons_in_holes(m, n):
    Input: m and n are Python integers.
    Given m pigeons and n holes, returns
    a specification that says that m pigeons are in
    n holes.
    Hint: you can do this by making a list of n holes,
    each of which is a z3.Int.

- two_in_hole(n):
    Input: n is a Python integers.
    Given m pigeons and n holes, returns
    a specification that says that at least one hole
    has two pigeons.

First, implement these two functions.
There is a test case that will help check that
your implementation is correct.
Then, answer the questions at the end of the file.
"""

import z3

def pigeons_in_holes(m, n):
    # A starting point: let's create a list of n holes
    holes = [z3.Int(f"hole{i}") for i in range(n)]
    # TODO
    raise NotImplementedError

def two_in_hole(n):
    holes = [z3.Int(f"hole{i}") for i in range(n)]
    # TODO
    raise NotImplementedError

def pigeonhole_principle(n):
    # TODO
    raise NotImplementedError

for i in range(1,10):
    n = 2**i
    print(f"=== Pigeonhole principle for n = {n} ===")
    spec = pigeonhole_principle(n)
    z3.prove(spec)

"""
Finally, here is a version of the pigeonhole principle
that is general enough to work for any n, instead of
just a specific n.

For this version, we use the z3.Array type
to encode an arbitrary number of holes.
"""

def pigeonhole_principle_general():
    n = z3.Int('n')
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    # TODO

"""
Let's see what happens when we try to prove this.
"""

z3.prove(pigeonhole_principle_general())
