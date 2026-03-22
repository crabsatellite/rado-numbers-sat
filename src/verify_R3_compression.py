"""Verify proof claims for R_3(x+3y=3z) = 27.

The equation is x + 3y = 3z, i.e. a=1, b=3, c=3.
k=3 colors, and the claim is R_3 = 3^3 = 27.

This script verifies the compression proof steps:
(a)-(c): Partial assignment propagation on {1,...,17}
(d): Consecutive multiples of 3 must share color
(e): Full compression: multiples of 3 use at most 2 colors on {1,...,26}
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from encoder import var, encode_rado_instance
from pysat.solvers import Cadical153


def add_color_assignment(solver, j, c, k):
    """Force integer j to color c."""
    solver.add_clause([var(c, j, k)])
    # Exclude other colors
    for i in range(k):
        if i != c:
            solver.add_clause([-var(i, j, k)])


def test_partial_assignment(chi_assignments, n, k, label):
    """Test if a partial color assignment is satisfiable on {1,...,n} with k colors.
    chi_assignments: list of (integer, color) pairs.
    """
    a, b, c_eq = 1, 3, 3
    clauses, num_vars, solutions = encode_rado_instance(a, b, c_eq, k, n, symmetry_breaking=False)

    solver = Cadical153()
    for cl in clauses:
        solver.add_clause(cl)

    for j, c in chi_assignments:
        add_color_assignment(solver, j, c, k)

    result = solver.solve()
    status = "SAT" if result else "UNSAT"
    solver.delete()
    print(f"  {label}: {status}")
    return result


def test_consecutive_multiples_different_color(m1, m2, n, k):
    """Test if forcing multiples m1 and m2 of 3 to different colors is UNSAT on {1,...,n}."""
    a, b, c_eq = 1, 3, 3
    clauses, num_vars, solutions = encode_rado_instance(a, b, c_eq, k, n, symmetry_breaking=False)

    solver = Cadical153()
    for cl in clauses:
        solver.add_clause(cl)

    # For each color assignment where m1 and m2 differ, we need to check ALL differ.
    # Encode: NOT(same color). For each color c, forbid both having c.
    # Actually we want to force them to DIFFERENT colors and check SAT/UNSAT.
    # chi(m1) != chi(m2): for each color c, NOT(both have c)
    for c in range(k):
        solver.add_clause([-var(c, m1, k), -var(c, m2, k)])

    result = solver.solve()
    status = "SAT" if result else "UNSAT"
    solver.delete()
    return result, status


def test_compression(n, k):
    """Test if multiples of 3 in {1,...,n} can be forced to use at most 2 colors."""
    a, b, c_eq = 1, 3, 3
    clauses, num_vars, solutions = encode_rado_instance(a, b, c_eq, k, n, symmetry_breaking=False)

    multiples = [m for m in range(3, n+1, 3)]
    print(f"\n  Multiples of 3 in {{1,...,{n}}}: {multiples}")

    # For each pair of colors (i,j) with i<j, test if all multiples can use only colors i,j
    # Actually: "at most 2 colors" means there exists some set of 2 colors.
    # We test: for each choice of excluded color c, is it SAT that no multiple gets color c?

    for excluded_c in range(k):
        solver = Cadical153()
        for cl in clauses:
            solver.add_clause(cl)

        # Forbid excluded color for all multiples of 3
        for m in multiples:
            solver.add_clause([-var(excluded_c, m, k)])

        result = solver.solve()
        status = "SAT" if result else "UNSAT"
        print(f"  Exclude color {excluded_c} from multiples: {status}")
        solver.delete()
        if result:
            return True, excluded_c

    # Try: ALL multiples must use same color
    print("\n  Testing: all multiples forced to same color...")
    for forced_c in range(k):
        solver = Cadical153()
        for cl in clauses:
            solver.add_clause(cl)
        for m in multiples:
            add_color_assignment(solver, m, forced_c, k)
        result = solver.solve()
        status = "SAT" if result else "UNSAT"
        print(f"  All multiples = color {forced_c}: {status}")
        solver.delete()

    # Also test: can we force all consecutive multiples to share color?
    print("\n  Testing: consecutive multiples forced to same color (chain)...")
    solver = Cadical153()
    for cl in clauses:
        solver.add_clause(cl)
    for i in range(len(multiples) - 1):
        m1, m2 = multiples[i], multiples[i+1]
        # m1 and m2 same color: for each color c, (m1=c) => (m2=c)
        # Equivalent: for each c, (-var(c,m1) OR var(c,m2)) AND (var(c,m1) OR -var(c,m2))
        for c in range(k):
            solver.add_clause([-var(c, m1, k), var(c, m2, k)])
            solver.add_clause([var(c, m1, k), -var(c, m2, k)])
    result = solver.solve()
    status = "SAT" if result else "UNSAT"
    print(f"  All consecutive multiples same color (chain): {status}")
    solver.delete()

    return False, None


if __name__ == "__main__":
    k = 3
    print("=" * 60)
    print("VERIFICATION: R_3(x + 3y = 3z) = 27 compression proof")
    print("=" * 60)

    # (a)-(c): Partial assignments on {1,...,17}
    n = 17
    base_assignments = [(3, 0), (6, 1), (4, 2), (8, 2)]

    print(f"\n--- Parts (a)-(c): chi(3)=0, chi(6)=1, chi(4)=2, chi(8)=2 on {{1,...,{n}}} ---")
    print(f"Testing chi(14)=0,1,2 respectively:\n")

    for c14 in range(3):
        assignments = base_assignments + [(14, c14)]
        label = f"chi(14)={c14}"
        test_partial_assignment(assignments, n, k, label)

    # (d): Consecutive multiples of 3 forced different => UNSAT?
    n_d = 26
    print(f"\n--- Part (d): Consecutive multiples of 3, different colors, on {{1,...,{n_d}}} ---\n")

    pairs = [(3, 6), (6, 9), (9, 12), (12, 15), (15, 18), (18, 21), (21, 24)]
    for m1, m2 in pairs:
        result, status = test_consecutive_multiples_different_color(m1, m2, n_d, k)
        print(f"  chi({m1}) != chi({m2}): {status}")

    # (e): Full compression on {1,...,26}
    print(f"\n--- Part (e): Compression — multiples of 3 use at most 2 colors on {{1,...,{n_d}}} ---")
    success, excluded = test_compression(n_d, k)
    if success:
        print(f"\n  RESULT: Compression possible (can exclude color {excluded} from multiples)")
    else:
        print(f"\n  RESULT: Cannot restrict multiples to only 2 colors")

    # Additional: verify R_3 = 27 directly
    print(f"\n--- Direct verification: R_3(x+3y=3z) ---")
    for n_test in [26, 27]:
        clauses, num_vars, solutions = encode_rado_instance(1, 3, 3, k, n_test)
        solver = Cadical153()
        for cl in clauses:
            solver.add_clause(cl)
        result = solver.solve()
        status = "SAT" if result else "UNSAT"
        print(f"  n={n_test}: {status} (R_3 {'>' if result else '<='} {n_test})")
        solver.delete()
