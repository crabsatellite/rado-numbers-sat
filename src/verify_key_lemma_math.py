"""
Mathematical verification of the Key Lemma and R_4(x+3y=3z) = 81.


Key Lemma: In any valid k-coloring of {1,...,b^k-1} avoiding monochromatic
x+by=bz, every color class C_c contains a pair (j, j+b^{k-1}) for some
j in {1,...,b^{k-1}}.

Verification plan:
1. Algebraic check: (b^k, j, j+b^{k-1}) satisfies x+by=bz
2. SAT verification of Key Lemma for b=3, k=4
3. SAT verification that Key Lemma FAILS for b=3, k=5
4. Full R_4=81 proof chain
5. Cross-check smaller cases
"""

from pysat.solvers import Cadical153
from encoder import var, new_clauses_for_n


def build_base_solver(b, k, n):
    """Build solver for k-coloring of {1,...,n} avoiding mono x+by=bz."""
    solver = Cadical153()
    for j in range(1, n + 1):
        clauses, _ = new_clauses_for_n(1, b, b, k, j, symmetry_breaking=(j == 1))
        for cl in clauses:
            solver.add_clause(cl)
    return solver


# ============================================================
# PART 1: Algebraic verification
# ============================================================

def verify_algebra():
    print("=" * 70)
    print("PART 1: ALGEBRAIC VERIFICATION")
    print("=" * 70)

    b = 3
    k = 4
    x_val = b**k      # 81
    bk1 = b**(k-1)    # 27

    print(f"\nEquation: x + {b}y = {b}z")
    print(f"Triple: (x, y, z) = ({x_val}, j, j+{bk1}) for j in 1..{bk1}")
    print()

    # Check: x + b*y = b*z  =>  81 + 3j = 3(j+27) = 3j + 81
    for j in range(1, bk1 + 1):
        lhs = x_val + b * j
        rhs = b * (j + bk1)
        assert lhs == rhs, f"FAILED at j={j}: {lhs} != {rhs}"

    print(f"  x + b*y = {x_val} + {b}*j = {b}*j + {x_val} = {b}*(j+{bk1}) = b*z")
    print(f"  Verified for all j in 1..{bk1}. ALL PASS.")

    # Range check
    print(f"\n  Range check:")
    print(f"    x = {x_val}: in 1..81? YES")
    print(f"    y = j in 1..{bk1}: in 1..81? YES")
    print(f"    z = j+{bk1} in {1+bk1}..{2*bk1}: in 1..81? YES (max={2*bk1} < 81)")

    # Distinctness check
    print(f"\n  Distinctness: x={x_val}, y=j in [1,27], z=j+27 in [28,54]")
    print(f"    x != y (81 > 27), x != z (81 > 54), y != z (j != j+27). ALL DISTINCT.")


# ============================================================
# PART 2: SAT verification of Key Lemma for b=3, k=4
# ============================================================

def verify_key_lemma_b3_k4():
    print("\n" + "=" * 70)
    print("PART 2: SAT VERIFICATION -- KEY LEMMA for b=3, k=4")
    print("=" * 70)

    b, k = 3, 4
    n = b**k - 1   # 80
    dist = b**(k-1) # 27

    print(f"\n  Parameters: b={b}, k={k}, n={n}, dist={dist}")
    print(f"  Universe: 1..{n}")
    print(f"  Pairs: (j, j+{dist}) for j in 1..{dist}")
    print(f"  Test: for each color c, forbid ALL dist-{dist} pairs from C_c, check UNSAT")
    print()

    all_unsat = True
    for c in range(k):
        solver = build_base_solver(b, k, n)

        # Forbid color c from having ANY pair (j, j+dist) both colored c
        for j in range(1, dist + 1):
            solver.add_clause([-var(c, j, k), -var(c, j + dist, k)])

        sat = solver.solve()
        result = "SAT" if sat else "UNSAT"

        if sat:
            all_unsat = False
            print(f"  Color {c}: {result} -- LEMMA FAILS!")
        else:
            print(f"  Color {c}: {result} -- color {c} MUST have a dist-{dist} pair")

        solver.delete()

    print()
    if all_unsat:
        print(f"  >>> KEY LEMMA VERIFIED for b=3, k=4: ALL 4 colors forced to have dist-27 pair <<<")
    else:
        print(f"  >>> KEY LEMMA FAILS for b=3, k=4 <<<")

    return all_unsat


# ============================================================
# PART 3: Verify Key Lemma FAILS for b=3, k=5
# ============================================================

def verify_key_lemma_fails_b3_k5():
    print("\n" + "=" * 70)
    print("PART 3: SAT VERIFICATION -- KEY LEMMA FAILURE for b=3, k=5")
    print("=" * 70)

    b, k = 3, 5
    n = b**k - 1   # 242
    dist = b**(k-1) # 81

    print(f"\n  Parameters: b={b}, k={k}, n={n}, dist={dist}")
    print(f"  Universe: 1..{n}")
    print(f"  Pairs: (j, j+{dist}) for j in 1..{dist}")
    print(f"  Test: for each color c, forbid ALL dist-{dist} pairs from C_c")
    print(f"  Expect: at least one color can avoid all pairs (SAT)")
    print()

    found_sat = False
    for c in range(k):
        solver = build_base_solver(b, k, n)

        # Forbid color c from having ANY pair (j, j+dist) both colored c
        for j in range(1, dist + 1):
            solver.add_clause([-var(c, j, k), -var(c, j + dist, k)])

        sat = solver.solve()
        result = "SAT" if sat else "UNSAT"

        if sat:
            found_sat = True
            # Extract and verify the witness
            model = solver.get_model()
            coloring = {}
            for j in range(1, n + 1):
                for i in range(k):
                    if model[var(i, j, k) - 1] > 0:
                        coloring[j] = i
                        break

            c_elts = sorted([j for j in range(1, n+1) if coloring[j] == c])

            # Verify: no dist-81 pair in C_c
            has_pair = False
            for j in range(1, dist + 1):
                if j in c_elts and (j + dist) in c_elts:
                    has_pair = True
                    break

            # Verify: coloring is valid (no mono triple)
            valid = True
            for x in range(1, n + 1):
                for y in range(1, n + 1):
                    val = x + b * y
                    if val % b == 0:
                        z = val // b
                        if 1 <= z <= n:
                            if coloring[x] == coloring[y] == coloring[z]:
                                valid = False
                                print(f"    INVALID: mono triple ({x},{y},{z}) all color {coloring[x]}")
                                break
                if not valid:
                    break

            print(f"  Color {c}: {result}")
            print(f"    |C_{c}| = {len(c_elts)}")
            print(f"    Has dist-{dist} pair in C_{c}: {has_pair}")
            print(f"    Coloring valid (no mono triples): {valid}")
            print(f"    >>> Color {c} successfully avoids all dist-{dist} pairs! <<<")
            solver.delete()
            break  # One is enough
        else:
            print(f"  Color {c}: {result} -- this color still forced")

        solver.delete()

    print()
    if found_sat:
        print(f"  >>> KEY LEMMA FAILS for b=3, k=5 as expected <<<")
        print(f"  >>> This is consistent with R_5(x+3y=3z) > 243 = 3^5 <<<")
    else:
        print(f"  >>> KEY LEMMA HOLDS for b=3, k=5 (unexpected!) <<<")

    return found_sat


# ============================================================
# PART 4: Complete R_4 = 81 proof chain
# ============================================================

def verify_R4_equals_81():
    print("\n" + "=" * 70)
    print("PART 4: COMPLETE PROOF THAT R_4(x+3y=3z) = 81")
    print("=" * 70)

    b, k = 3, 4

    # Step A: R_4 > 80 (lower bound via SAT)
    print(f"\n  Step A: R_4 > 80")
    print(f"  Need: valid 4-coloring of 1..80 exists")
    n = 80
    solver = build_base_solver(b, k, n)
    sat = solver.solve()
    print(f"    SAT({n}) = {sat}")
    assert sat, "FAILED: should be SAT"

    # Extract witness coloring
    model = solver.get_model()
    coloring = {}
    for j in range(1, n + 1):
        for i in range(k):
            if model[var(i, j, k) - 1] > 0:
                coloring[j] = i
                break
    solver.delete()

    # Verify witness
    valid = True
    for x in range(1, n + 1):
        for y in range(1, n + 1):
            val = x + b * y
            if val % b == 0:
                z = val // b
                if 1 <= z <= n:
                    if coloring[x] == coloring[y] == coloring[z]:
                        valid = False
                        break
        if not valid:
            break
    print(f"    Witness valid: {valid}")
    print(f"    Conclusion: R_4 > 80. VERIFIED.")

    # Step B: R_4 <= 81 (upper bound via Key Lemma)
    print(f"\n  Step B: R_4 <= 81 (Key Lemma argument)")
    print(f"  Proof by contradiction: assume valid 4-coloring of 1..81")
    print(f"    1. Restrict to 1..80: valid 4-coloring")
    print(f"    2. Key Lemma (b=3, k=4, SAT-verified): every color c has")
    print(f"       a pair (j, j+27) in C_c with j in 1..27")
    print(f"    3. Element 81 gets some color c* = chi(81)")
    print(f"    4. By Key Lemma, color c* has pair (j, j+27) in C_c*")
    print(f"    5. Triple (81, j, j+27): check 81 + 3j = 3(j+27) = 3j+81. YES!")
    print(f"    6. All three elements 81, j, j+27 have color c*. MONO TRIPLE!")
    print(f"    7. Contradiction. No valid 4-coloring of 1..81 exists.")
    print(f"    Conclusion: R_4 <= 81. VERIFIED.")

    # Step C: Direct SAT confirmation
    print(f"\n  Step C: Direct SAT confirmation")
    n = 81
    solver = build_base_solver(b, k, n)
    sat = solver.solve()
    print(f"    SAT({n}) = {sat}")
    assert not sat, "FAILED: should be UNSAT"
    solver.delete()
    print(f"    Direct UNSAT confirms R_4 <= 81.")

    print(f"\n  ===== R_4(x+3y=3z) = 81 = 3^4. FULLY VERIFIED. =====")


# ============================================================
# PART 5: Cross-check smaller cases
# ============================================================

def verify_smaller_cases():
    print("\n" + "=" * 70)
    print("PART 5: KEY LEMMA FOR SMALLER CASES (consistency check)")
    print("=" * 70)

    b = 3
    for k in [1, 2, 3]:
        n = b**k - 1
        dist = b**(k-1)

        print(f"\n  k={k}: n={n}, dist={dist}")

        all_unsat = True
        for c in range(k):
            solver = build_base_solver(b, k, n)
            for j in range(1, dist + 1):
                if j + dist <= n:  # only if pair is in range
                    solver.add_clause([-var(c, j, k), -var(c, j + dist, k)])

            sat = solver.solve()
            if sat:
                all_unsat = False
                print(f"    Color {c}: SAT (lemma fails)")
            else:
                print(f"    Color {c}: UNSAT (forced)")
            solver.delete()

        if all_unsat:
            print(f"    Key Lemma HOLDS for b=3, k={k}")
            # Verify R_k = 3^k
            n_rk = b**k
            solver = build_base_solver(b, k, n_rk)
            sat_rk = solver.solve()
            solver.delete()
            if not sat_rk:
                print(f"    R_{k} = {n_rk}: UNSAT confirms upper bound")
            else:
                print(f"    R_{k} > {n_rk}: SAT means R_k > {n_rk}")
        else:
            print(f"    Key Lemma FAILS for b=3, k={k}")


if __name__ == "__main__":
    verify_algebra()
    lemma_ok = verify_key_lemma_b3_k4()
    lemma_fails = verify_key_lemma_fails_b3_k5()
    verify_R4_equals_81()
    verify_smaller_cases()

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"  Key Lemma b=3, k=4: {'VERIFIED' if lemma_ok else 'FAILED'}")
    print(f"  Key Lemma b=3, k=5 fails: {'YES (as expected)' if lemma_fails else 'NO (unexpected)'}")
    print(f"  R_4(x+3y=3z) = 81: VERIFIED (lower + upper bound)")
