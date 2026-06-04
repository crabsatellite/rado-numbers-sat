"""Verify the paper's Distance Pair Lemma slab and emit a result manifest.


For each paper case (k=3, b=3..10) and (k=4, b=3..5), this script checks
the SAT formula used by Lemma `lem:keypair`: a valid k-coloring of
{1,...,b^k-1} avoiding x + by = bz, plus clauses forcing one target color
to avoid every pair (j, j+b^(k-1)). UNSAT for every target color proves
that no color can avoid the required distance pair.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

from pysat.solvers import Cadical153

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from encoder import encode_rado_instance, var  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "data" / "results" / "dpl_paper_slab_verification.json"
PAPER_CASES = [(b, 3) for b in range(3, 11)] + [(b, 4) for b in range(3, 6)]


def parse_case(text: str) -> tuple[int, int]:
    parts = text.replace(",", ":").split(":")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("case must be b:k, for example 5:4")
    try:
        b, k = (int(parts[0]), int(parts[1]))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("case values must be integers") from exc
    if b < 2 or k < 1:
        raise argparse.ArgumentTypeError("case requires b >= 2 and k >= 1")
    return b, k


def parse_colors(text: str | None, k: int) -> list[int]:
    if text is None or text == "all":
        return list(range(k))
    colors = []
    for raw in text.split(","):
        color = int(raw.strip())
        if color < 0 or color >= k:
            raise ValueError(f"color {color} outside 0..{k - 1}")
        colors.append(color)
    return colors


def load_existing(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {
            "lemma": "Distance Pair Lemma (paper slab)",
            "solver": "CaDiCaL 1.5.3 via pysat.solvers.Cadical153",
            "equation_family": "x + by = bz",
            "symmetry_breaking": "chi(1)=0, with every target color checked; any counterexample can be color-relabelled into this slice",
            "cases": [],
        }
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def write_manifest(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)
        f.write("\n")
    tmp.replace(path)


def case_key(b: int, k: int) -> str:
    return f"b={b},k={k}"


def upsert_case(payload: dict[str, Any], case_result: dict[str, Any]) -> None:
    key = case_result["case"]
    cases = payload.setdefault("cases", [])
    for idx, existing in enumerate(cases):
        if existing.get("case") == key:
            cases[idx] = case_result
            return
    cases.append(case_result)


def verify_one_color(
    *,
    b: int,
    k: int,
    n: int,
    dist: int,
    color: int,
    base_clauses: list[list[int]],
) -> dict[str, Any]:
    solver = Cadical153()
    for clause in base_clauses:
        solver.add_clause(clause)

    pair_clause_count = 0
    for j in range(1, dist + 1):
        solver.add_clause([-var(color, j, k), -var(color, j + dist, k)])
        pair_clause_count += 1

    start = time.time()
    sat = solver.solve()
    elapsed = time.time() - start
    stats: dict[str, Any] = {}
    try:
        accum = solver.accum_stats()
        if isinstance(accum, dict):
            stats = dict(accum)
    except Exception:  # noqa: BLE001
        pass
    solver.delete()

    return {
        "color": color,
        "status": "SAT" if sat else "UNSAT",
        "time_s": elapsed,
        "num_pair_blocking_clauses": pair_clause_count,
        "solver_stats": stats,
    }


def verify_case(
    *,
    b: int,
    k: int,
    colors: list[int],
    output: Path,
    payload: dict[str, Any],
) -> dict[str, Any]:
    n = b**k - 1
    dist = b ** (k - 1)
    print(f"\n=== DPL case b={b}, k={k}: n={n}, dist={dist} ===", flush=True)

    base_start = time.time()
    base_clauses, num_vars, solutions = encode_rado_instance(
        a=1, b=b, c=b, k=k, n=n, symmetry_breaking=True
    )
    base_elapsed = time.time() - base_start
    print(
        f"Base CNF: vars={num_vars}, clauses={len(base_clauses)}, "
        f"rado_triples={len(solutions)}, build_time={base_elapsed:.3f}s",
        flush=True,
    )

    case_result = {
        "case": case_key(b, k),
        "b": b,
        "k": k,
        "n": n,
        "distance": dist,
        "num_vars": num_vars,
        "num_base_clauses": len(base_clauses),
        "num_rado_triples_in_domain": len(solutions),
        "base_build_time_s": base_elapsed,
        "per_color_results": [],
        "all_checked_colors_unsat": False,
        "complete_for_all_colors": False,
    }

    for color in colors:
        result = verify_one_color(
            b=b,
            k=k,
            n=n,
            dist=dist,
            color=color,
            base_clauses=base_clauses,
        )
        case_result["per_color_results"].append(result)
        print(
            f"  color {color}: {result['status']} in {result['time_s']:.3f}s",
            flush=True,
        )
        case_result["all_checked_colors_unsat"] = all(
            r["status"] == "UNSAT" for r in case_result["per_color_results"]
        )
        case_result["complete_for_all_colors"] = sorted(
            r["color"] for r in case_result["per_color_results"]
        ) == list(range(k))
        upsert_case(payload, case_result)
        refresh_summary(payload)
        write_manifest(output, payload)
        if result["status"] != "UNSAT":
            break

    return case_result


def refresh_summary(payload: dict[str, Any]) -> None:
    cases = payload.get("cases", [])
    payload["num_cases"] = len(cases)
    payload["complete"] = all(c.get("complete_for_all_colors") for c in cases)
    payload["all_cases_unsat"] = all(
        c.get("all_checked_colors_unsat") and c.get("complete_for_all_colors")
        for c in cases
    )
    times = [
        r.get("time_s", 0.0)
        for c in cases
        for r in c.get("per_color_results", [])
        if isinstance(r.get("time_s"), (int, float))
    ]
    payload["max_per_color_time_s"] = max(times) if times else None
    payload["total_solver_time_s"] = sum(times)
    payload["updated_at_unix"] = time.time()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--case",
        dest="cases",
        action="append",
        type=parse_case,
        help="Restrict to a case b:k. Repeatable. Default is the full paper slab.",
    )
    parser.add_argument(
        "--colors",
        default=None,
        help="Comma-separated target colors for a single case, or 'all'.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"Output JSON manifest (default: {DEFAULT_OUTPUT})",
    )
    args = parser.parse_args()

    cases = args.cases if args.cases else PAPER_CASES
    payload = load_existing(args.output)
    payload["paper_cases_expected"] = [case_key(b, k) for b, k in PAPER_CASES]
    payload["run_started_at_unix"] = time.time()

    for b, k in cases:
        colors = parse_colors(args.colors, k)
        verify_case(b=b, k=k, colors=colors, output=args.output, payload=payload)

    refresh_summary(payload)
    payload["run_finished_at_unix"] = time.time()
    write_manifest(args.output, payload)

    if args.cases:
        # Targeted runs may intentionally be partial.
        return 0 if all(
            c.get("all_checked_colors_unsat")
            for c in payload.get("cases", [])
            if c.get("case") in {case_key(b, k) for b, k in cases}
        ) else 1

    return 0 if payload.get("complete") and payload.get("all_cases_unsat") else 1


if __name__ == "__main__":
    sys.exit(main())
