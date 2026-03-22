"""Verify R_5(x+3y=3z) > 243 = 3^5.

If confirmed, this means:
1. The conjecture R_k(x+3y=3z) = 3^k fails at k=5.
2. The proof attempt was on the right track: the Key Lemma fails at k=5
   because the conjecture itself fails.
3. We need to find the actual value of R_5.

VERIFICATION PLAN:
1. Extract the 5-coloring of {1,...,243} and verify it manually.
2. Find R_5 by binary search.
"""

import time
import json
from pysat.solvers import Cadical153
from encoder import var, new_clauses_for_n


def v3(n):
    if n == 0:
        return float('inf')
    v = 0
    while n % 3 == 0:
        v += 1
        n //= 3
    return v


def build_solver_b(b, k, n):
    solver = Cadical153()
    for j in range(1, n + 1):
        clauses, _ = new_clauses_for_n(1, b, b, k, j, symmetry_breaking=True)
        for cl in clauses:
            solver.add_clause(cl)
    return solver


def extract_coloring(solver, k, n):
    model = solver.get_model()
    coloring = {}
    for j in range(1, n + 1):
        for i in range(k):
            if model[var(i, j, k) - 1] > 0:
                coloring[j] = i
                break
    return coloring


def verify_coloring(coloring, b, n):
    """Verify a coloring has no monochromatic solution to x+by=bz."""
    violations = []
    for d in range(1, n):
        x = b * d
        if x > n:
            break
        for y in range(1, n - d + 1):
            z = y + d
            if x <= n and y <= n and z <= n:
                if coloring[x] == coloring[y] == coloring[z]:
                    violations.append((x, y, z, coloring[x]))
                    if len(violations) >= 5:
                        return violations
    return violations


def find_R5():
    """Find R_5(x+3y=3z) by incremental search from 243."""
    b, k = 3, 5

    print("=" * 70)
    print("FINDING R_5(x+3y=3z)")
    print("=" * 70)

    # We know n=242 is SAT (v_3 coloring). Try n=243.
    n = 243
    print(f"\n  n={n}: ", end="", flush=True)
    solver = build_solver_b(b, k, n)
    t0 = time.time()
    sat = solver.solve()
    elapsed = time.time() - t0
    print(f"{'SAT' if sat else 'UNSAT'} ({elapsed:.1f}s)")

    if sat:
        coloring = extract_coloring(solver, k, n)
        # Verify!
        violations = verify_coloring(coloring, b, n)
        if violations:
            print(f"  VERIFICATION FAILED! Violations: {violations[:3]}")
            solver.delete()
            return
        else:
            print(f"  Verified: coloring is valid!")
            # Save the witness
            with open('../data/results/R5_witness_243.json', 'w') as f:
                json.dump({
                    'n': n, 'k': k, 'b': b,
                    'valid': True,
                    'coloring': {str(j): coloring[j] for j in range(1, n+1)},
                    'color_sizes': {str(c): sum(1 for j in range(1, n+1) if coloring[j] == c) for c in range(k)},
                }, f, indent=2)
            print(f"  Saved witness to ../data/results/R5_witness_243.json")
    solver.delete()

    if not sat:
        print(f"  R_5 = 243 (confirmed)")
        return 243

    # n=243 is SAT. Binary search for R_5.
    lo, hi = 244, 800  # R_5 is somewhere above 243

    # First: quick check at some powers
    for test_n in [250, 270, 300, 350, 400, 500, 729]:
        print(f"\n  n={test_n}: ", end="", flush=True)
        solver = build_solver_b(b, k, test_n)
        t0 = time.time()
        sat = solver.solve()
        elapsed = time.time() - t0
        print(f"{'SAT' if sat else 'UNSAT'} ({elapsed:.1f}s)")

        if sat:
            coloring = extract_coloring(solver, k, test_n)
            violations = verify_coloring(coloring, b, test_n)
            if violations:
                print(f"  VERIFICATION FAILED!")
            else:
                print(f"  Valid coloring found.")
        else:
            print(f"  R_5 <= {test_n}")
            hi = test_n
            solver.delete()
            break

        solver.delete()

    # Binary search between lo and hi
    print(f"\n  Binary search: R_5 in [{lo}, {hi}]")
    while lo < hi:
        mid = (lo + hi) // 2
        print(f"\n  n={mid}: ", end="", flush=True)
        solver = build_solver_b(b, k, mid)
        t0 = time.time()
        sat = solver.solve()
        elapsed = time.time() - t0
        print(f"{'SAT' if sat else 'UNSAT'} ({elapsed:.1f}s)")

        if sat:
            lo = mid + 1
        else:
            hi = mid

        solver.delete()

    print(f"\n  R_5(x+3y=3z) = {lo}")
    return lo


def main():
    R5 = find_R5()

    if R5 and R5 != 243:
        print(f"\n" + "=" * 70)
        print(f"CONCLUSION: R_5(x+3y=3z) = {R5} != 3^5 = 243")
        print(f"The conjecture R_k(x+by=bz) = b^k FAILS for b=3, k=5.")
        print(f"This parallels the b=2 anomaly (R_3(x+2y=2z) = 14 != 8).")
        print(f"=" * 70)


if __name__ == '__main__':
    main()
