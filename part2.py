"""
Four numbers game solver

In the second part of the homework, we will implement
a solver for the four numbers game.

=== Four numbers game ===

The game works as follows:
First, I secretly think of two positive integers x and y.
I don't tell you what they are, but instead I give you four
numbers:
    a, b, c, d
and tell you that they are the values of the sum, difference,
product, and quotient (x+y, x-y, xy, and x/y), in an unknown order.
Assume that the difference is nonnegative and the quotient is a whole number.

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
For simplicity, assume that all 4 numbers are nonnegative integers.
You can get input in Python using the `input` function:
    num1 = int(input("First number: "))

=== Output, part (a) ===

Use Z3 to output the
solution (x and y), if it finds one,
or say that there are no solutions.
You can assume that x and y are positive integers.

The first function q5a(a, b, c, d) should, when given four integers a, b, c, d, return a solution $x, y$, if there is at least one solution, or None if there is no solution.
Second, the function q5_interactive() should provide an interactive version: it should prompt the user for 4 numbers, then display as output the correct answers x and y.

=== Output, part (b) ===

Use Z3 to determine
whether there are any *other* solutions, besides
the one that you found in the first stage.

q5b(a, b, c, d) should return a Python string "multiple", "unique", or "none" depending on whether multiple solutions exist.
Update your q5_run() interactive version to also show the output of q5b.
=== Helper function ===

Please use the helper function get_solution
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

def q5a(a, b, c, d):
    # TODO
    raise NotImplementedError

def q5_run(a, b, c, d):
    a, b, c, d = get_input()
    print("=== Stage 1 ===")
    # TODO, call your solution for part (a), print the solution
    print("=== Stage 2 ===")
    # TODO, call your solution for part (b), print the solution

    raise NotImplementedError

def q5b(a, b, c, d):
    # TODO
    raise NotImplementedError

def solve_stage2(a, b, c, d):
    print("=== Stage 2 ===")
    # TODO: Determine if there are any other solutions
    raise NotImplementedError

if __name__ == "__main__":
    q5_run()
