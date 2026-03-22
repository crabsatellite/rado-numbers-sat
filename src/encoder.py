"""SAT encoder for k-color Rado numbers.

Encodes the question: does there exist a k-coloring of {1,...,n}
with no monochromatic solution to a given linear equation?

Reference: Ahmed, Zaman, Bright (2025) "Symbolic Sets for Proving
Bounds on Rado Numbers", arxiv:2505.12085.
"""


def var(color, integer, k):
    """Variable index for 'integer j has color i'.

    Args:
        color: color index, 0-based (0 to k-1)
        integer: the integer value, 1-based (1 to n)
        k: number of colors

    Returns:
        1-based DIMACS variable index
    """
    return (integer - 1) * k + color + 1


def encode_coloring_constraints(k, n):
    """Generate clauses ensuring each integer in {1,...,n} gets exactly one color.

    Returns list of clauses (each clause is a list of signed integers).
    """
    clauses = []
    for j in range(1, n + 1):
        # At-least-one-color
        clauses.append([var(i, j, k) for i in range(k)])
        # At-most-one-color (pairwise)
        for i1 in range(k):
            for i2 in range(i1 + 1, k):
                clauses.append([-var(i1, j, k), -var(i2, j, k)])
    return clauses


def find_solutions_axby_eq_cz(a, b, c, n):
    """Find all solutions (x, y, z) in {1,...,n} to ax + by = cz.

    For the Rado number problem, we need x, y, z to be positive integers
    in {1,...,n}. They need NOT be distinct (unless the equation forces it).
    """
    solutions = []
    for x in range(1, n + 1):
        for y in range(1, n + 1):
            val = a * x + b * y
            if val % c == 0:
                z = val // c
                if 1 <= z <= n:
                    solutions.append((x, y, z))
    return solutions


def encode_no_monochromatic(k, solutions):
    """For each solution and each color, forbid all variables being that color.

    For a solution (x, y, z) and color i:
        NOT(v_{i,x}) OR NOT(v_{i,y}) OR NOT(v_{i,z})
    """
    clauses = []
    for (x, y, z) in solutions:
        for i in range(k):
            clause = [-var(i, x, k), -var(i, y, k), -var(i, z, k)]
            # Deduplicate literals (when x=y or y=z etc.)
            clause = list(dict.fromkeys(clause))
            clauses.append(clause)
    return clauses


def encode_symmetry_breaking(k):
    """Symmetry breaking: force integer 1 to color 0."""
    return [[var(0, 1, k)]]


def encode_rado_instance(a, b, c, k, n, symmetry_breaking=True):
    """Full SAT encoding for: is there a k-coloring of {1,...,n}
    with no monochromatic solution to ax + by = cz?

    SAT means: such a coloring exists (R_k > n).
    UNSAT means: no such coloring exists (R_k <= n).

    Returns (clauses, num_vars, solutions).
    """
    num_vars = k * n
    clauses = []

    # Coloring constraints
    clauses.extend(encode_coloring_constraints(k, n))

    # Find all solutions to the equation in {1,...,n}
    solutions = find_solutions_axby_eq_cz(a, b, c, n)

    # Forbid monochromatic solutions
    clauses.extend(encode_no_monochromatic(k, solutions))

    # Symmetry breaking
    if symmetry_breaking:
        clauses.extend(encode_symmetry_breaking(k))

    return clauses, num_vars, solutions


def new_clauses_for_n(a, b, c, k, n, symmetry_breaking=True):
    """Generate ONLY the new clauses needed when extending from n-1 to n.

    This is for incremental solving: we add integer n to the universe.
    New clauses:
    1. Coloring constraints for integer n
    2. No-monochromatic clauses for NEW solutions involving integer n

    A solution (x, y, z) is "new" if at least one of x, y, z equals n
    (and none exceeds n). We use direct O(n) formula computation.
    """
    clauses = []

    # Coloring for new integer n
    clauses.append([var(i, n, k) for i in range(k)])
    for i1 in range(k):
        for i2 in range(i1 + 1, k):
            clauses.append([-var(i1, n, k), -var(i2, n, k)])

    # Symmetry breaking for n=1
    if n == 1 and symmetry_breaking:
        clauses.append([var(0, 1, k)])

    # Collect new solutions using set to avoid duplicates
    new_solutions = set()

    # Case 1: z = n. For each x in [1,n], solve ax + by = cn for y.
    # y = (cn - ax) / b. Need y >= 1 and y <= n.
    cn = c * n
    for x in range(1, n + 1):
        rem = cn - a * x
        if rem > 0 and rem % b == 0:
            y = rem // b
            if 1 <= y <= n:
                new_solutions.add((x, y, n))

    # Case 2: x = n. For each y in [1,n], solve an + by = cz for z.
    # z = (an + by) / c.
    an = a * n
    for y in range(1, n + 1):
        val = an + b * y
        if val % c == 0:
            z = val // c
            if 1 <= z <= n:
                new_solutions.add((n, y, z))

    # Case 3: y = n. For each x in [1,n], solve ax + bn = cz for z.
    # z = (ax + bn) / c.
    bn = b * n
    for x in range(1, n + 1):
        val = a * x + bn
        if val % c == 0:
            z = val // c
            if 1 <= z <= n:
                new_solutions.add((x, n, z))

    clauses.extend(encode_no_monochromatic(k, new_solutions))
    return clauses, new_solutions
