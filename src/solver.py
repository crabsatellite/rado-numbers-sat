"""Incremental SAT solver for Rado numbers using PySAT + CaDiCaL.

Computes R_k(ax + by = cz) by incrementally adding integers 1, 2, 3, ...
until the SAT instance becomes UNSAT.

Reference encoding: Ahmed, Zaman, Bright (2025), arxiv:2505.12085.
"""

import json
import time
import logging
from pathlib import Path

from pysat.solvers import Cadical153

from encoder import var, new_clauses_for_n


logger = logging.getLogger(__name__)


def compute_rado_number(a, b, c, k, max_n=100000, symmetry_breaking=True,
                        log_interval=100, timeout_s=72000):
    """Compute R_k(ax + by = cz) via incremental SAT solving.

    Returns dict with result and metadata.
    """
    start_time = time.time()
    solver = Cadical153()

    total_clauses = 0
    total_solutions = 0

    for n in range(1, max_n + 1):
        elapsed = time.time() - start_time
        if elapsed > timeout_s:
            solver.delete()
            return {
                "equation": f"{a}x + {b}y = {c}z",
                "k": k,
                "result": None,
                "status": "timeout",
                "last_sat_n": n - 1,
                "elapsed_s": round(elapsed, 2),
                "total_clauses": total_clauses,
            }

        # Add new clauses for integer n
        clauses, new_sols = new_clauses_for_n(a, b, c, k, n, symmetry_breaking)
        for clause in clauses:
            solver.add_clause(clause)
        total_clauses += len(clauses)
        total_solutions += len(new_sols)

        # Solve
        sat = solver.solve()

        if n % log_interval == 0 or not sat:
            elapsed = time.time() - start_time
            logger.info(
                f"n={n:>6d}  SAT={sat}  clauses={total_clauses:>10d}  "
                f"solutions={total_solutions:>8d}  elapsed={elapsed:.1f}s"
            )

        if not sat:
            elapsed = time.time() - start_time
            solver.delete()
            return {
                "equation": f"{a}x + {b}y = {c}z",
                "coefficients": {"a": a, "b": b, "c": c},
                "k": k,
                "result": n,
                "status": "solved",
                "elapsed_s": round(elapsed, 2),
                "total_clauses": total_clauses,
                "total_solutions": total_solutions,
            }

    solver.delete()
    return {
        "equation": f"{a}x + {b}y = {c}z",
        "k": k,
        "result": None,
        "status": "max_n_reached",
        "max_n": max_n,
        "elapsed_s": round(time.time() - start_time, 2),
    }


def run_single(a, b, c, k, max_n=100000, results_dir="data/results",
               logs_dir="logs"):
    """Run a single Rado number computation with full logging."""
    results_dir = Path(results_dir)
    logs_dir = Path(logs_dir)
    results_dir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    # Set up file logging
    log_file = logs_dir / f"R{k}_{a}x+{b}y={c}z.log"
    file_handler = logging.FileHandler(log_file, mode="w")
    file_handler.setFormatter(
        logging.Formatter("%(asctime)s %(message)s", datefmt="%H:%M:%S")
    )
    logger.addHandler(file_handler)
    logger.setLevel(logging.INFO)

    # Also log to console
    console = logging.StreamHandler()
    console.setFormatter(logging.Formatter("%(message)s"))
    logger.addHandler(console)

    logger.info(f"Computing R_{k}({a}x + {b}y = {c}z)")
    logger.info(f"Max n: {max_n}, Solver: CaDiCaL 1.5.3 (incremental)")
    logger.info("=" * 60)

    result = compute_rado_number(a, b, c, k, max_n=max_n)

    logger.info("=" * 60)
    if result["status"] == "solved":
        logger.info(f"RESULT: R_{k}({a}x + {b}y = {c}z) = {result['result']}")
    else:
        logger.info(f"STATUS: {result['status']}")
    logger.info(f"Time: {result['elapsed_s']}s")

    # Save result
    result_file = results_dir / f"R{k}_{a}x+{b}y={c}z.json"
    with open(result_file, "w") as f:
        json.dump(result, f, indent=2)
    logger.info(f"Saved: {result_file}")

    # Clean up handlers
    logger.removeHandler(file_handler)
    logger.removeHandler(console)
    file_handler.close()

    return result


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Compute Rado number R_k(ax+by=cz)")
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--b", type=int, required=True)
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--k", type=int, default=4, help="Number of colors")
    parser.add_argument("--max-n", type=int, default=100000)
    args = parser.parse_args()

    run_single(args.a, args.b, args.c, args.k, max_n=args.max_n)
