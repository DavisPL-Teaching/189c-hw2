"""
Part 1: Mini exercises
"""

import z3
import pytest

from helper import prove, solve, SAT, UNSAT, PROVED, COUNTEREXAMPLE, UNKNOWN

"""
A. Writing specifications

Consider the absolute value function
that we discussed in lecture:
"""

def abs(x):
    return z3.If(x >= 0, x, -x)

"""
Write a specification for the following properties using Z3.

You can use the PROVED, FAILED, and COUNTEREXAMPLE
constants for assertions in your tests.
For example, if a property fails, use
    assert prove(spec) == COUNTEREXAMPLE

1. If x is greater than or equal to 0, then the absolute value of x is equal to x.

2. If x is less than y, then the absolute value of x is less than the absolute value of y.

3. If x is equal to y + 1, then the absolute value of x is equal to 1 plus the absolute value of y.

4. The absolute value applied twice (absolute value of the absolute value of x) is equal to the absolute value of x.

5. The absolute value of x + y is less than or equal to the absolute value of x + the absolute value of y.

The first one is written for you.
"""

def test_abs_1():
    x = z3.Int('x')
    spec = z3.Implies(x >= 0, abs(x) == x)
    assert prove(spec) == PROVED

@pytest.mark.skip
def test_abs_2():
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_abs_3():
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_abs_4():
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_abs_5():
    # TODO
    raise NotImplementedError

"""
B. Rectangle collision calculator

Let's write a function that is able to calculate
whether two rectangles collide.
Initially, the two rectangles
are given by a width, height, position of the center
(in (x, y) coordinates), and velocity (in (vx, vy) coordinates).
Over time, they move in the direction of the velocity every second.

6. Write a function rectangle_position that calculates
the position of a rectangle at a given time t,
as a Z3 expression.

7. Write a function rectangles_overlap that creates a formula whether
two rectangles overlap at a specific time. The formula
should be satisfiable if the two rectangles overlap and
unsatisfiable if they do not overlap.
(The time is not given as an argument, because it should be
included in the expressions for the rectangle's position.)

Hint:
There's more than one way to do this, but one way that is
more general than just rectangles is to create two new variables,
    overlap_point_x
    overlap_point_y
that describe the point of overlap between the two shapes.

8. Write a function rectangles_collide that checks whether
two rectangles collide at any point in time.

Your function should return true if there exists *at least one* input
    (t, overlap_point_x, overlap_point_y)
that makes the two rectangles overlap.

Hint: You may want to call solve(...).
You can use the constants SAT and UNSAT to check the output.
"""

def rectangle_position(x, y, vx, vy, t):
    """
    x, y, vx, vy: Python integers
    t: a Z3 real number

    returns: a tuple of two Z3 expressions
        (x, y)
    that represents the center of the rectangle at time t.
    """
    # TODO
    raise NotImplementedError

def rectangles_overlap(
    x1, y1, width1, height1,
    x2, y2, width2, height2,
):
    """
    x1, y1, width1, height1: Z3 expressions
    x2, y2, width2, height2: Z3 expressions

    returns: a Z3 expression that is satisfiable if the two
    rectangles overlap.
    """
    # TODO
    raise NotImplementedError

def rectangles_collide(
    x1, y1, width1, height1, vx1, vy1,
    x2, y2, width2, height2, vx2, vy2,
):
    """
    x1, y1, width1, height1, vx1, vy1: Python integers
    x2, y2, width2, height2, vx2, vy2: Python integers

    returns: True if the two rectangles collide at any point in time.

    This function should use our solve function.
    """
    # TODO
    raise NotImplementedError

"""
9. Write a unit test for rectangles_collide to
check if it seems to be working.
"""

@pytest.mark.skip
def test_rectangles_collide():
    # TODO
    raise NotImplementedError

"""
10. Do you think this is the best way to check for collisions in general?
For example, for collision detection in a game?
What about for a simple prototype?
Discuss one benefit and one drawback of this approach.
"""
