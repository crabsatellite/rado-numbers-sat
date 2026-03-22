"""Cross-verification of claimed R_k values for x + by = bz.

Tests:
  b=3: R_2=9, R_3=27, R_4=81 (claimed b^k pattern)
  b=4: R_4=256 (claimed 4^4)
  b=2: R_4=56 (claimed anomaly, not 2^4=16)

Uses incremental CaDiCaL via PySAT, same encoder as main project.
Timeout: 600s per computation.
"""

import sys
import time
from pysat.solvers import Cadical153
from encoder import new_clauses_for_n


def find_rado_number(a, b_coeff, c, k, max_n=500, timeout_s=600):
    """Find R_k(ax + by = cz) by incremental SAT solving.

    Returns (R_k, elapsed_seconds) or (None, elapsed) on timeout/max_n.
    """
    start = time.time()
    solver = Cadical153()

    for n in range(1, max_n + 1):
        elapsed = time.time() - start
        if elapsed > timeout_s:
            solver.delete()
            return None, elapsed, f"timeout at n={n}"

        clauses, _ = new_clauses_for_n(a, b_coeff, c, k, n, symmetry_breaking=True)
        for cl in clauses:
            solver.add_clause(cl)

        sat = solver.solve()

        if not sat:
            elapsed = time.time() - start
            solver.delete()
            return n, elapsed, "solved"

    elapsed = time.time() - start
    solver.delete()
    return None, elapsed, f"max_n={max_n} reached (still SAT)"


def main():
    # For equation x + by = bz: a=1, b_coeff=b, c=b
    tests = [
        # (b, k, claimed_value, description)
        (3, 2, 9,   "b=3, k=2: claimed R_2=9=3^2"),
        (3, 3, 27,  "b=3, k=3: claimed R_3=27=3^3"),
        (3, 4, 81,  "b=3, k=4: claimed R_4=81=3^4"),
        (4, 4, 256, "b=4, k=4: claimed R_4=256=4^4"),
        (2, 4, 56,  "b=2, k=4: claimed R_4=56 (anomaly, not 2^4=16)"),
    ]

    print("=" * 70)
    print("CROSS-VERIFICATION: R_k(x + by = bz)")
    print("Solver: CaDiCaL 1.5.3 (incremental), Timeout: 600s")
    print("=" * 70)

    results = []
    for b, k, claimed, desc in tests:
        print(f"\n--- {desc} ---")
        print(f"Equation: x + {b}y = {b}z, k={k}, max_n={max(300, claimed+50)}")
        sys.stdout.flush()

        max_n = max(300, claimed + 50)
        R_k, elapsed, status = find_rado_number(1, b, b, k, max_n=max_n, timeout_s=600)

        if R_k is not None:
            match = "MATCH" if R_k == claimed else f"MISMATCH (got {R_k}, claimed {claimed})"
            print(f"  R_{k}(x+{b}y={b}z) = {R_k}  [{match}]  time={elapsed:.2f}s")
        else:
            print(f"  FAILED: {status}  time={elapsed:.2f}s")

        results.append((desc, R_k, claimed, elapsed, status))
        sys.stdout.flush()

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    all_match = True
    for desc, R_k, claimed, elapsed, status in results:
        if R_k is not None:
            ok = "OK" if R_k == claimed else "FAIL"
            if R_k != claimed:
                all_match = False
            print(f"  [{ok}] {desc}: computed={R_k}, claimed={claimed}, time={elapsed:.2f}s")
        else:
            all_match = False
            print(f"  [??] {desc}: {status}, time={elapsed:.2f}s")

    print(f"\nAll claims verified: {all_match}")


if __name__ == "__main__":
    main()
