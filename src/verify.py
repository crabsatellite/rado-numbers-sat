"""Verify SAT encoder against known Rado numbers."""

import sys
import time
from solver import compute_rado_number


KNOWN = [
    # (a, b, c, k, expected, label)
    (1, 1, 1, 2, 5, "S(2) = R_2(x+y=z)"),
    (1, 1, 1, 3, 14, "S(3) = R_3(x+y=z)"),
    (1, 1, 1, 4, 45, "S(4) = R_4(x+y=z)"),
    # Malo's 4-color results: x1+x2+c=x3 => x+y=z with offset
    # x+y+1=z is the same as 1*x + 1*y + 1 = 1*z, but our encoder
    # handles ax+by=cz (homogeneous). For inhomogeneous, we rewrite:
    # x+y+c=z => x+y = z-c. Not directly our format.
    # Instead verify more Schur-like: 2x+y=z (R_2 should be small)
    (2, 1, 1, 2, None, "R_2(2x+y=z) - compute"),
    (1, 1, 2, 2, None, "R_2(x+y=2z) - compute"),
]


def run_verification():
    print("=" * 60)
    print("Verification of SAT encoder against known Rado numbers")
    print("=" * 60)

    all_pass = True
    for a, b, c, k, expected, label in KNOWN:
        print(f"\n{label}: R_{k}({a}x + {b}y = {c}z)")
        t0 = time.time()
        result = compute_rado_number(a, b, c, k, max_n=1000, log_interval=10000)
        elapsed = time.time() - t0

        actual = result["result"]
        status = result["status"]

        if expected is not None:
            match = "PASS" if actual == expected else "FAIL"
            if actual != expected:
                all_pass = False
            print(f"  Expected: {expected}, Got: {actual}, {match}  [{elapsed:.2f}s]")
        else:
            print(f"  Computed: {actual} ({status})  [{elapsed:.2f}s]")

    print("\n" + "=" * 60)
    if all_pass:
        print("ALL VERIFICATION TESTS PASSED")
    else:
        print("SOME TESTS FAILED")
        sys.exit(1)


if __name__ == "__main__":
    run_verification()
