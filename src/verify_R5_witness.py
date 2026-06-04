"""Independent verification of R5 witnesses for x + 3y = 3z.

"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PATH = ROOT / "data" / "results" / "R5_witness_296.json"


def load_witness(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def verify_witness(path: Path) -> bool:
    data = load_witness(path)

    b = int(data.get("b", 3))
    n = int(data["n"])
    k = int(data["k"])
    chi = {int(key): int(val) for key, val in data["coloring"].items()}

    print(f"=== R5 Witness Verification: {path} ===")
    print(f"Equation: x + {b}y = {b}z on {{1,...,{n}}} with {k} colors")

    valid_colors = set(range(k))
    missing = [i for i in range(1, n + 1) if i not in chi]
    bad_color = [(i, chi[i]) for i in chi if chi[i] not in valid_colors]
    extra = [i for i in chi if i < 1 or i > n]

    print("\n[Check 1] Domain and range")
    print(f"  Integers 1..{n} present: {len(chi) == n and not missing}")
    if missing:
        print(f"  MISSING: {missing[:20]}...")
    if bad_color:
        print(f"  BAD COLORS: {bad_color[:20]}...")
    if extra:
        print(f"  EXTRA keys outside [1,{n}]: {extra[:20]}...")
    print(f"  All colors in {{0,...,{k-1}}}: {not bad_color}")

    color_counts = Counter(chi.values())
    print("\n[Check 2] Color class sizes")
    for color in range(k):
        print(f"  Color {color}: {color_counts.get(color, 0)} elements")
    print(f"  Total: {sum(color_counts.values())}")
    stored_sizes = {int(key): int(val) for key, val in data.get("color_sizes", {}).items()}
    if stored_sizes:
        match = all(color_counts.get(color, 0) == stored_sizes.get(color, 0) for color in range(k))
        print(f"  Matches stored color_sizes: {match}")

    print("\n[Check 3] Symmetry breaking")
    print(f"  chi(1) = {chi.get(1, 'MISSING')} (expected 0: {chi.get(1) == 0})")

    triples: list[tuple[int, int, int]] = []
    mono_triples: list[tuple[int, int, int]] = []
    for d in range(1, n // b + 1):
        x = b * d
        for y in range(1, n - d + 1):
            z = y + d
            triples.append((x, y, z))
            if chi[x] == chi[y] == chi[z]:
                mono_triples.append((x, y, z))

    print(f"\n[Check 4] Equation x + {b}y = {b}z")
    print(f"  Total valid triples (x,y,z) in {{1,...,{n}}}: {len(triples)}")
    print(f"  Monochromatic triples: {len(mono_triples)}")

    if mono_triples:
        print(f"\n  *** VERIFICATION FAILED: found {len(mono_triples)} monochromatic triple(s) ***")
        for x, y, z in mono_triples[:10]:
            print(
                f"    ({x}, {y}, {z}): chi = ({chi[x]}, {chi[y]}, {chi[z]}), "
                f"check: {x} + {b}*{y} = {x + b * y}, {b}*{z} = {b * z}"
            )
    else:
        print("\n  *** VERIFICATION PASSED: no monochromatic triples ***")

    degenerate = sum(1 for x, y, z in triples if x == y or y == z or x == z)
    print(f"\n  Degenerate triples (some equal): {degenerate}")

    print("\n[Sanity] First 5 triples:")
    for x, y, z in triples[:5]:
        print(
            f"  x={x}, y={y}, z={z}: {x}+{b}*{y}={x + b * y}, {b}*{z}={b * z}, "
            f"colors=({chi[x]},{chi[y]},{chi[z]})"
        )

    valid_domain = not missing and not bad_color and not extra
    valid = valid_domain and not mono_triples
    print("\n=== SUMMARY ===")
    print(f"  Valid coloring: {valid_domain}")
    print(f"  Zero monochromatic triples: {not mono_triples}")
    print(f"  Witness is {'VALID' if valid else 'INVALID'}")
    return valid


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        default=[DEFAULT_PATH],
        help="Witness JSON path(s) to verify.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    ok = True
    for path in args.paths:
        if not path.is_absolute():
            path = Path.cwd() / path
        ok = verify_witness(path) and ok
        print()
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
