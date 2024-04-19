"""
Part 3: Pigeonhole Principle

This part will explore the performance of Z3.
This part will explore some of the limitations of Z3.
What are some questions that are too difficult for Z3?

While we won't see the z3.unknown ("I don't know") answer
in this part, we will instead explore a problem for
which Z3 can take a long time or a lot of memory to solve
(or both).
A famous problem that solvers like Z3 sometimes have
difficulty with is the pigeonhole principle.

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
