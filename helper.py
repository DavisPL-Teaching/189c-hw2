"""
Z3 helper functions

We will use these instead of
z3.prove and z3.solve.
The main difference between z3.prove and
z3.solve is that they also return the result.

We also provide a function get_solution
that will be useful for Part 2.
"""

import z3

## Constants
SAT = z3.sat
UNSAT = z3.unsat
UNKNOWN = z3.unknown
PROVED = UNSAT
COUNTEREXAMPLE = SAT

"""
prove(spec)

Returns PROVED, COUNTEREXAMPLE, or UNKNOWN
"""
def prove(spec):
    solver = z3.Solver()
    solver.add(z3.Not(spec))
    result = solver.check()
    if result == UNSAT:
        print("proved")
    elif result == UNKNOWN:
        print("failed to prove")
    else:
        # result == SAT
        print("counterexample")
        print(solver.model())
    return result

"""
solve(spec)

Returns SAT, UNSAT, or UNKNOWN
"""
def solve(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == UNSAT:
        print("no solution")
    elif result == UNKNOWN:
        print("failed to solve")
    else:
        # result == SAT
        print("solution found")
        print(solver.model())
    return result

"""
get_solution(spec)

If the spec is satisfiable,
this returns the solution as a Z3 "Model" object.

You can get the value of a variable x by doing
    model[x]

Here is an example usage:
    x = z3.Int('x')
    spec = x > 5
    model = get_solution(spec)
    print(model[x])

Returns: either a Z3 model solution or None
"""

def get_solution(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == SAT:
        return solver.model()
    else:
        return None
