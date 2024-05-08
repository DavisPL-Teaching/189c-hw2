"""
Four numbers game solver

In the second part of the homework, we will implement
a solver for the four numbers game.
(We tried out this game in Lecture 0.)

=== Four numbers game ===

The game works as follows:
First, I secretly think of two positive integers x and y.
I don't tell you what they are, but instead I give you four
numbers:
    a, b, c, d
and tell you that they are the values of the sum, difference,
product, and quotient (x+y, x-y, xy, and x/y), in an unknown order.

Can you figure out what x and y are?

=== Examples ===

Four numbers: 20, 95, 105, 500
Solution: x = 5, y = 100.

Four numbers: 2, 6, 18, 72
Solution: x = 12, y = 6.

Four numbers: 0, 1, 1, 2
Solution: x = 1, y = 1.

=== Input ===

Your solver should take 4 numbers as input from the user.
For simplicity, assume that all 4 numbers are positive integers.
You can get input in Python using the `input` function:
    num1 = int(input("First number: "))

=== Output, first stage ===

In the first stage, use Z3 to output the
solution (x and y), if it finds one,
or say that there are no solutions.
You can assume that x and y are positive integers.

=== Output, second stage ===

In the second stage, use Z3 to determine
whether there are any *other* solutions, besides
the one that you found in the first stage.

You may change the function signature for part 2
if you find that different arguments would be more useful.

=== Helper function ===

We have provided a function get_solution
in helper.py that will be useful for this part.
If the spec is satisfiable (SAT), it will return
a solution that you can use to get the values of x and y:
    x = Int('x')
    x_val = get_solution(spec)[x]

=== Try it out! ===

Try out your game by running
    python3 part2.py

to see if it works!

If you like, you can also write unit tests, but this
is not required for this part.
"""

import z3
import pytest

from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

def get_input():
    print("=== Input ===")
    # TODO: return (a, b, c, d)
    raise NotImplementedError

def solve_stage1(a, b, c, d):
    print("=== Stage 1 ===")
    # TODO: Solve the four numbers game
    raise NotImplementedError

def solve_stage2(a, b, c, d):
    print("=== Stage 2 ===")
    # TODO: Determine if there are any other solutions
    raise NotImplementedError

if __name__ == "__main__":
    a, b, c, d = get_input()
    solve_stage1(a, b, c, d)
    solve_stage2(a, b, c, d)
