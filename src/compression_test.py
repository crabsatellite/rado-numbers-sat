"""Test Color Compression Lemma via SAT.

Color Compression Lemma: In any valid k-coloring of {1,...,b^k - 1}
avoiding monochromatic x + by = bz, the multiples of b use at most k-1 colors.

We test this by encoding: exists a valid k-coloring of {1,...,b^k - 1}
where multiples of b use ALL k colors? If UNSAT, compression holds.

We also extract structural information from SAT witnesses when compression
fails (e.g., b=2).
"""

import sys
import time
from pysat.solvers import Cadical153
from encoder import var, new_clauses_for_n


def test_compression(b, k, verbose=True):
    """Test whether Color Compression holds for given b, k.

    Returns dict with:
        holds: True if UNSAT (compression proved), False if SAT
        time_s: time taken
        witness: if SAT, the coloring of multiples
    """
    n = b**k - 1
    a_coeff, b_coeff, c_coeff = 1, b, b  # equation x + by = bz

    if verbose:
        print(f"Testing Color Compression: b={b}, k={k}, n={n}")
        print(f"  Multiples of {b} in {{1,...,{n}}}: {[j for j in range(b, n+1, b)]}")

    # Build full encoding for {1,...,n}
    solver = Cadical153()
    all_solutions = set()

    for j in range(1, n + 1):
        clauses, new_sols = new_clauses_for_n(a_coeff, b_coeff, c_coeff, k, j,
                                               symmetry_breaking=True)
        all_solutions.update(new_sols)
        for cl in clauses:
            solver.add_clause(cl)

    # Now add constraint: multiples of b use ALL k colors.
    # For each color i, there exists some multiple m*b with that color.
    multiples = [j for j in range(b, n + 1, b)]

    if verbose:
        print(f"  Number of multiples: {len(multiples)}")
        print(f"  Adding constraint: every color appears in multiples")

    for i in range(k):
        # At least one multiple has color i
        clause = [var(i, m, k) for m in multiples]
        solver.add_clause(clause)

    t0 = time.time()
    sat = solver.solve()
    elapsed = time.time() - t0

    result = {
        'b': b, 'k': k, 'n': n,
        'holds': not sat,
        'time_s': round(elapsed, 4),
    }

    if sat:
        model = solver.get_model()
        # Extract coloring of multiples
        mult_colors = {}
        for m in multiples:
            for i in range(k):
                if model[var(i, m, k) - 1] > 0:
                    mult_colors[m] = i
                    break
        result['mult_colors'] = mult_colors
        colors_used = set(mult_colors.values())
        result['colors_in_multiples'] = len(colors_used)

        if verbose:
            print(f"  SAT! Compression FAILS for b={b}, k={k}")
            print(f"  Multiples coloring: {mult_colors}")
            print(f"  Colors used in multiples: {colors_used}")
    else:
        if verbose:
            print(f"  UNSAT! Compression HOLDS for b={b}, k={k}")

    if verbose:
        print(f"  Time: {elapsed:.4f}s")

    solver.delete()
    return result


def test_partial_compression(b, k, num_colors_forced, verbose=True):
    """Test if multiples can use exactly num_colors_forced colors.

    This helps understand the tight bound on color usage in multiples.
    """
    n = b**k - 1
    a_coeff, b_coeff, c_coeff = 1, b, b

    if verbose:
        print(f"\nTesting: b={b}, k={k}, can multiples use {num_colors_forced} colors?")

    solver = Cadical153()

    for j in range(1, n + 1):
        clauses, _ = new_clauses_for_n(a_coeff, b_coeff, c_coeff, k, j,
                                        symmetry_breaking=True)
        for cl in clauses:
            solver.add_clause(cl)

    multiples = [j for j in range(b, n + 1, b)]

    # Force exactly num_colors_forced colors by:
    # 1. Require first num_colors_forced colors to appear
    # 2. Forbid remaining colors
    # (With symmetry breaking color 0 is already used by integer 1,
    #  so we force colors 0..num_colors_forced-1 to appear in multiples)

    for i in range(num_colors_forced):
        clause = [var(i, m, k) for m in multiples]
        solver.add_clause(clause)

    # Forbid colors num_colors_forced..k-1 in multiples
    for i in range(num_colors_forced, k):
        for m in multiples:
            solver.add_clause([-var(i, m, k)])

    t0 = time.time()
    sat = solver.solve()
    elapsed = time.time() - t0

    if verbose:
        print(f"  {'SAT (possible)' if sat else 'UNSAT (impossible)'} in {elapsed:.4f}s")

    solver.delete()
    return sat


def analyze_coloring_structure(b, k, verbose=True):
    """For valid colorings, analyze what colors appear in multiples.

    Enumerate a few valid colorings and check color distribution.
    """
    n = b**k - 1
    a_coeff, b_coeff, c_coeff = 1, b, b

    if verbose:
        print(f"\nAnalyzing coloring structure: b={b}, k={k}, n={n}")

    solver = Cadical153()

    for j in range(1, n + 1):
        clauses, _ = new_clauses_for_n(a_coeff, b_coeff, c_coeff, k, j,
                                        symmetry_breaking=True)
        for cl in clauses:
            solver.add_clause(cl)

    multiples = [j for j in range(b, n + 1, b)]

    # Find up to 50 valid colorings and analyze
    colorings_found = 0
    max_colors_in_mults = 0
    color_counts = {}

    while colorings_found < 50:
        if not solver.solve():
            break

        model = solver.get_model()
        colorings_found += 1

        # Extract coloring
        coloring = {}
        for j in range(1, n + 1):
            for i in range(k):
                if model[var(i, j, k) - 1] > 0:
                    coloring[j] = i
                    break

        # Colors in multiples
        mult_cols = set(coloring[m] for m in multiples)
        nc = len(mult_cols)
        max_colors_in_mults = max(max_colors_in_mults, nc)
        color_counts[nc] = color_counts.get(nc, 0) + 1

        # Block this coloring
        blocking = [-model[var(coloring[j], j, k) - 1] for j in range(1, n + 1)]
        solver.add_clause(blocking)

    if verbose:
        print(f"  Found {colorings_found} colorings")
        print(f"  Max colors in multiples: {max_colors_in_mults}")
        print(f"  Distribution: {color_counts}")
        print(f"  Compression holds: {max_colors_in_mults < k}")

    solver.delete()
    return {
        'b': b, 'k': k, 'n': n,
        'colorings_found': colorings_found,
        'max_colors_in_mults': max_colors_in_mults,
        'distribution': color_counts,
        'compression_holds': max_colors_in_mults < k
    }


def run_systematic_tests():
    """Run systematic Color Compression tests."""
    print("=" * 60)
    print("SYSTEMATIC COLOR COMPRESSION TESTS")
    print("Equation: x + by = bz")
    print("=" * 60)

    results = []

    # Test all feasible (b, k) pairs
    test_cases = [
        # (b, k) - n = b^k - 1
        (2, 2),   # n=3
        (2, 3),   # n=7
        (2, 4),   # n=15
        (3, 2),   # n=8
        (3, 3),   # n=26
        (3, 4),   # n=80
        (4, 2),   # n=15
        (4, 3),   # n=63
        (5, 2),   # n=24
        (5, 3),   # n=124
        (6, 2),   # n=35
        (6, 3),   # n=215
        (7, 2),   # n=48
        (7, 3),   # n=342
    ]

    print("\n--- Full Compression Tests (all k colors forced in multiples) ---\n")

    for b, k_val in test_cases:
        n = b**k_val - 1
        if n > 400:
            print(f"  Skipping b={b}, k={k_val}: n={n} too large")
            continue
        r = test_compression(b, k_val)
        results.append(r)
        print()

    # Summary table
    print("\n" + "=" * 60)
    print("SUMMARY TABLE")
    print("=" * 60)
    print(f"{'b':>3} {'k':>3} {'n':>6} {'Compression':>15} {'Time':>10}")
    print("-" * 40)
    for r in results:
        status = "HOLDS" if r['holds'] else "FAILS"
        print(f"{r['b']:>3} {r['k']:>3} {r['n']:>6} {status:>15} {r['time_s']:>10.4f}s")

    # Now do structure analysis for small cases
    print("\n\n--- Coloring Structure Analysis ---\n")
    small_cases = [(3, 3), (3, 4), (4, 3), (5, 3)]
    for b, k_val in small_cases:
        n = b**k_val - 1
        if n <= 130:
            analyze_coloring_structure(b, k_val)

    # Partial compression: what's the max colors in multiples for b=2?
    print("\n\n--- Partial Compression for b=2 ---\n")
    for k_val in [3, 4]:
        for nc in range(1, k_val + 1):
            test_partial_compression(2, k_val, nc)


if __name__ == '__main__':
    run_systematic_tests()
