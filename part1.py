"""
Part 1: Mini exercises
"""

import z3

"""
Helper functions

You can use these instead of
z3.prove and z3.solve.
The main difference between z3.prove and
z3.solve is that they also return the result.
"""

def prove(spec):
    solver = z3.Solver()
    solver.add(z3.Not(spec))
    result = solver.check()
    if result == z3.unsat:
        print("proved")
    elif result == z3.unknown:
        print("failed to prove")
        print(s.model())
    else:
        print("counterexample")
        print(s.model())
    return result

def solve(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == z3.unsat:
        print("no solution")
    elif result == z3.unknown:
        print("failed to solve")
    else:
        print("solution found")
        print(s.model())
    return result

"""
A. Writing specifications

Consider the absolute value function
that we discussed in lecture. Write a specification
for the following properties, and use Z3 to check
which of them hold.
The first one is written for you.
"""

def abs(x):
    return z3.If(x >= 0, x, -x)

"""
1. If x is greater than or equal to 0, then the absolute value of x is equal to x.

2. If x is less than y, then the absolute value of x is less than the absolute value of y.

4. If x is equal to 2 * y, then the absolute value of x is equal to 2 times the absolute value of y.

5. The absolute value of the absolute value of x is equal to the absolute value of -x.

6. The absolute value of x + y is less than or equal to the absolute value of x + the absolute value of y.
"""

"""
B. Rectangle collision calculator

Let's write a function that is able to calculate
whether two rectangles collide. The rectangles
are given by a width, height, position, and velocity.

7. Write the function rectangle_position that calculates
the position of a rectangle at a given time, as a Z3 expression.

8. Write the function rectangles_overlap that creates a formula whether
two rectangles overlap at a specific time. The formula
should be satisfiable if the two rectangles overlap and
unsatisfiable if they do not overlap.
Hint: You can create two new variables,
    overlap_point_x
    overlap_point_y
that describe the point of overlap between the two rectangles.

9. Write the function rectangles_collide that checks whether
two rectangles collide at any point in time.
The time is not given as an argument, because it should be
included in the expressions for the rectangle's position.

Your function should call s3.solve to check whether
there exists a point in time (t) and an overlap point
(overlap_point_x, overlap_point_y)
such that the two rectangles collide.

10. Write two unit tests for rectangles_collide.
"""

def rectangle_position(x, y, width, height, vx, vy, t):
    """
    x, y, width, height, vx, vy: Python integers
    t: a Z3 real number

    returns: a tuple of Z3 expressions
    that represents the position of the rectangle at time t.
    """
    # TODO
    raise NotImplementedError

def rectangles_overlap(x1, y1, width1, height1, vx1, vy1,
                       x2, y2, width2, height2, vx2, vy2):
     """
     x1, y1, width1, height1, vx1, vy1: Z3 expressions
     x2, y2, width2, height2, vx2, vy2: Z3 expressions

     returns: a Z3 expression that is satisfiable if the two
     rectangles overlap.
     """
     # TODO
     raise NotImplementedError

def rectangles_collide(x1, y1, width1, height1, vx1, vy1,
                       x2, y2, width2, height2, vx2, vy2):
    """
    x1, y1, width1, height1, vx1, vy1: Python integers
    x2, y2, width2, height2, vx2, vy2: Python integers

    returns: True if the two rectangles collide at any point in time.

    This function should use our solve function.
    """
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_rectangles_collide_1():
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_rectangles_collide_2():
    # TODO
    raise NotImplementedError
