# Hints

## Part 1 exercise 6

The `update_player_level_z3` version should return a Z3
expression for the result.

Remember that Python if corresponds to the Z3 expression
```
z3.If(cond, result1, result2)
```
(where `cond` is a z3 Boolean and `result1`, `result2` are Z3 expressions).

## Part 1 exercise 9

You can create two new variables,
    overlap_point_x
    overlap_point_y
that describe the point of overlap between the two rectangles.

It may help to recall the definition of satisfiable:
the formula is satisfiable if there exists *at least one* input
    (t, overlap_point_x, overlap_point_y)
that makes the two rectangles overlap.

## Part 1 exercise 10

Use solve(...) and the constants SAT and UNSAT to check the output.

## Part 1 exercise 13

You might define a `Shape` class with a method called
`in_shape(x, y)` that returns a Z3 formula that is true
if the point (x, y) is inside the shape.
You can have subclasses to implement the different shapes.

## Part 2 stage 1

You will need to consider many possibilities
for the order of the four numbers.
(There are 24 possible orders!)
If it helps, you can first sort the numbers [a, b, c, d]
and use that to narrow down the possibilities.

## Part 2 stage 2

You should add a constraint that the new solution is different
from the first solution. We saw an example of this in class.
To get the first solution, use the
`get_solution` function from `helper.py`.

## Part 3 exercise 1

Here is a starting point:
```
def pigeons_in_holes(m, n):
    # A starting point: this creates a list of n holes,
    # where the i-th element contains the number of pigeons
    # in hole i.
    # You can use holes[i] to get the value for hole i.
    holes = [z3.Int(f"hole{i}") for i in range(n)]
```

You need the total number of pigeons (sum variable) to be equal to m,
and the number of pigeons in each hole to be >= 0.

There may be multiple encodings, but this is probably the easiest one
and the one that Z3 performs best on.

## Part 3 exercise 5

If the test is taking longer than a couple of minutes,
you can assume that Z3 is too slow (timeout).

To time your code, instead of using a Python time library
you can just use the time command in the terminal:
```
time pytest part3.py
```

Skip all the tests except the one you're interested in.

## Part 3 exercise 7

Try changing the number of pigeons from n + 1 to n
or changing the required number of pigeons in a hole
from at least 2 to exactly 2.
If you are feeling creative, you can also try to come up with
a different change.
