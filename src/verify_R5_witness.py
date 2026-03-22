"""Independent verification of R5 witness for x + 3y = 3z on {1,...,243} with 5 colors."""

import json
from collections import Counter

def main():
    with open("../data/results/R5_witness_243.json") as f:
        data = json.load(f)

    n = data["n"]
    k = data["k"]
    chi = {int(key): val for key, val in data["coloring"].items()}

    print(f"=== R5 Witness Verification: x + 3y = 3z on {{1,...,{n}}} with {k} colors ===\n")

    # Check 1: every integer 1..n has exactly one color in {0,...,k-1}
    valid_colors = set(range(k))
    missing = []
    bad_color = []
    for i in range(1, n + 1):
        if i not in chi:
            missing.append(i)
        elif chi[i] not in valid_colors:
            bad_color.append((i, chi[i]))

    extra = [i for i in chi if i < 1 or i > n]

    print(f"[Check 1] Domain and range")
    print(f"  Integers 1..{n} present: {len(chi) == n and not missing}")
    if missing:
        print(f"  MISSING: {missing[:20]}...")
    if bad_color:
        print(f"  BAD COLORS: {bad_color[:20]}...")
    if extra:
        print(f"  EXTRA keys outside [1,{n}]: {extra[:20]}...")
    print(f"  All colors in {{0,...,{k-1}}}: {not bad_color}")

    # Check 2: color class sizes
    color_counts = Counter(chi.values())
    print(f"\n[Check 2] Color class sizes")
    for c in range(k):
        print(f"  Color {c}: {color_counts.get(c, 0)} elements")
    print(f"  Total: {sum(color_counts.values())}")
    stored_sizes = {int(kk): v for kk, v in data.get("color_sizes", {}).items()}
    if stored_sizes:
        match = all(color_counts.get(c, 0) == stored_sizes.get(c, 0) for c in range(k))
        print(f"  Matches stored color_sizes: {match}")

    # Check 3: chi(1) = 0? (symmetry breaking)
    print(f"\n[Check 3] Symmetry breaking")
    print(f"  chi(1) = {chi.get(1, 'MISSING')} (expected 0: {chi.get(1) == 0})")

    # Check 4: enumerate ALL triples (x, y, z) with x + 3y = 3z, all in {1,...,n}
    # Rearranging: x = 3z - 3y = 3(z - y), so x must be divisible by 3... NO.
    # x + 3y = 3z  =>  z = (x + 3y) / 3
    # We need z to be a positive integer in [1, n].
    # So x + 3y must be divisible by 3, i.e., x ≡ 0 (mod 3).
    # Also z = (x + 3y)/3 = x/3 + y, so if x = 3m then z = m + y.
    # We need x, y, z all distinct? Actually the equation doesn't require distinctness
    # unless specified. Let me enumerate all valid triples including where some may coincide.

    triples = []
    mono_triples = []

    for x in range(1, n + 1):
        for y in range(1, n + 1):
            s = x + 3 * y
            if s % 3 != 0:
                continue
            z = s // 3
            if z < 1 or z > n:
                continue
            # We have a valid triple: x + 3y = 3z
            triples.append((x, y, z))
            if chi[x] == chi[y] == chi[z]:
                mono_triples.append((x, y, z))

    print(f"\n[Check 4] Equation x + 3y = 3z")
    print(f"  Total valid triples (x,y,z) in {{1,...,{n}}}: {len(triples)}")
    print(f"  Monochromatic triples: {len(mono_triples)}")

    if mono_triples:
        print(f"\n  *** VERIFICATION FAILED: found {len(mono_triples)} monochromatic triple(s) ***")
        for t in mono_triples[:10]:
            x, y, z = t
            print(f"    ({x}, {y}, {z}): chi = ({chi[x]}, {chi[y]}, {chi[z]}), "
                  f"check: {x} + 3*{y} = {x + 3*y}, 3*{z} = {3*z}")
    else:
        print(f"\n  *** VERIFICATION PASSED: no monochromatic triples ***")

    # Additional: count triples where x=y or y=z or x=z
    degenerate = sum(1 for x, y, z in triples if x == y or y == z or x == z)
    print(f"\n  Degenerate triples (some equal): {degenerate}")

    # Sanity: spot-check a few triples
    print(f"\n[Sanity] First 5 triples:")
    for t in triples[:5]:
        x, y, z = t
        print(f"  x={x}, y={y}, z={z}: {x}+3*{y}={x+3*y}, 3*{z}={3*z}, "
              f"colors=({chi[x]},{chi[y]},{chi[z]})")

    # Check if x=y=z is ever a solution: x + 3x = 3x => x = 0, not in range. Good.
    # Check x=y: x + 3x = 3z => 4x = 3z => z = 4x/3. Only when x divisible by 3.

    print(f"\n=== SUMMARY ===")
    print(f"  Valid coloring: {not missing and not bad_color and not extra}")
    print(f"  Zero monochromatic triples: {len(mono_triples) == 0}")
    print(f"  Witness is {'VALID' if (not mono_triples and not missing and not bad_color) else 'INVALID'}")


if __name__ == "__main__":
    main()
