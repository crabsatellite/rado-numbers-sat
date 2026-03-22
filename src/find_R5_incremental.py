"""Find R_5(x+3y=3z) using incremental SAT solving.

Start from n=243 (known SAT) and increment until UNSAT.
This is much faster than building from scratch for each n.
"""

import time
import json
from pysat.solvers import Cadical153
from encoder import var, new_clauses_for_n


def find_R5_incremental():
    b, k = 3, 5
    start_n = 1
    max_n = 1000  # safety limit

    print("=" * 70)
    print("INCREMENTAL SEARCH FOR R_5(x+3y=3z)")
    print("=" * 70)

    solver = Cadical153()
    t0 = time.time()

    last_sat_n = 0
    for n in range(1, max_n + 1):
        clauses, new_sols = new_clauses_for_n(1, b, b, k, n, symmetry_breaking=True)
        for cl in clauses:
            solver.add_clause(cl)

        if n < 240:
            continue  # Skip known-SAT range

        sat = solver.solve()
        elapsed = time.time() - t0

        if n % 10 == 0 or not sat or n >= 243:
            status = 'SAT' if sat else 'UNSAT'
            print(f"  n={n:>4d}: {status} (cumulative {elapsed:.1f}s)")

        if sat:
            last_sat_n = n
        else:
            print(f"\n  R_5(x+3y=3z) = {n}")
            print(f"  Last SAT: n={last_sat_n}")
            print(f"  Total time: {elapsed:.1f}s")

            # Verify by checking n-1 is SAT
            solver.delete()
            solver2 = Cadical153()
            for j in range(1, n):
                clauses2, _ = new_clauses_for_n(1, b, b, k, j, symmetry_breaking=True)
                for cl in clauses2:
                    solver2.add_clause(cl)
            sat2 = solver2.solve()
            solver2.delete()

            if sat2:
                print(f"  Confirmed: n={n-1} is SAT")
            else:
                print(f"  WARNING: n={n-1} also UNSAT!")

            return n

    solver.delete()
    print(f"  Did not find UNSAT up to n={max_n}")
    return None


def main():
    R5 = find_R5_incremental()

    if R5:
        result = {
            'equation': 'x+3y=3z',
            'b': 3,
            'k': 5,
            'R5': R5,
            'b_k': 243,
            'match': R5 == 243,
        }
        print(f"\n  Result: R_5 = {R5}, 3^5 = 243, match = {R5 == 243}")

        with open('../data/results/R5_result.json', 'w') as f:
            json.dump(result, f, indent=2)
        print(f"  Saved to ../data/results/R5_result.json")


if __name__ == '__main__':
    main()
