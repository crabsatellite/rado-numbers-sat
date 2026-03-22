"""Parameter sweep for computing R_k tables across equation families.

Sweeps (a, b) values for equation families:
  Family 1: E(3,0;a,b,b) => ax + by = bz
  Family 2: E(3,0;a,a,b) => ax + ay = bz  (i.e., a(x+y) = bz)

Saves results incrementally and generates summary tables.
"""

import json
import time
import logging
from pathlib import Path
from datetime import datetime

from solver import compute_rado_number


logger = logging.getLogger("sweep")


def sweep_family1(k, a_max, b_max, max_n=100000, timeout_s=3600,
                  results_dir="data/results", logs_dir="logs"):
    """Sweep Family 1: ax + by = bz for a in [1,a_max], b in [1,b_max].

    Note: ax + by = bz is equivalent to ax = b(z-y). For a solution to exist
    with positive integers, we need z > y when a,b > 0.
    """
    results_dir = Path(results_dir)
    logs_dir = Path(logs_dir)
    results_dir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    summary_file = results_dir / f"family1_R{k}_summary.json"
    summary = _load_summary(summary_file)

    log_file = logs_dir / f"sweep_family1_R{k}_{datetime.now():%Y%m%d_%H%M%S}.log"
    _setup_logging(log_file)

    logger.info(f"Sweep Family 1: ax + by = bz, k={k}, a=[1,{a_max}], b=[1,{b_max}]")
    logger.info(f"Max n={max_n}, timeout={timeout_s}s per instance")
    logger.info("=" * 70)

    for a in range(1, a_max + 1):
        for b in range(1, b_max + 1):
            key = f"({a},{b})"
            if key in summary and summary[key]["status"] == "solved":
                logger.info(f"SKIP ({a},{b}): already solved = {summary[key]['result']}")
                continue

            logger.info(f"\n--- Computing R_{k}({a}x + {b}y = {b}z) ---")
            result = compute_rado_number(a, b, b, k, max_n=max_n,
                                         timeout_s=timeout_s, log_interval=500)
            summary[key] = result

            if result["status"] == "solved":
                logger.info(f"R_{k}({a}x + {b}y = {b}z) = {result['result']}  "
                           f"[{result['elapsed_s']:.1f}s]")
            else:
                logger.info(f"({a},{b}): {result['status']} [{result.get('elapsed_s', '?')}s]")

            # Save incrementally
            with open(summary_file, "w") as f:
                json.dump(summary, f, indent=2)

    _print_table(summary, "ax + by = bz", k, a_max, b_max)
    return summary


def sweep_family2(k, a_max, b_max, max_n=100000, timeout_s=3600,
                  results_dir="data/results", logs_dir="logs"):
    """Sweep Family 2: ax + ay = bz (i.e., a(x+y) = bz)."""
    results_dir = Path(results_dir)
    logs_dir = Path(logs_dir)
    results_dir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    summary_file = results_dir / f"family2_R{k}_summary.json"
    summary = _load_summary(summary_file)

    log_file = logs_dir / f"sweep_family2_R{k}_{datetime.now():%Y%m%d_%H%M%S}.log"
    _setup_logging(log_file)

    logger.info(f"Sweep Family 2: a(x+y) = bz, k={k}, a=[1,{a_max}], b=[1,{b_max}]")
    logger.info(f"Max n={max_n}, timeout={timeout_s}s per instance")
    logger.info("=" * 70)

    for a in range(1, a_max + 1):
        for b in range(1, b_max + 1):
            key = f"({a},{b})"
            if key in summary and summary[key]["status"] == "solved":
                logger.info(f"SKIP ({a},{b}): already solved = {summary[key]['result']}")
                continue

            logger.info(f"\n--- Computing R_{k}({a}x + {a}y = {b}z) ---")
            result = compute_rado_number(a, a, b, k, max_n=max_n,
                                         timeout_s=timeout_s, log_interval=500)
            summary[key] = result

            if result["status"] == "solved":
                logger.info(f"R_{k}({a}x + {a}y = {b}z) = {result['result']}  "
                           f"[{result['elapsed_s']:.1f}s]")
            else:
                logger.info(f"({a},{b}): {result['status']} [{result.get('elapsed_s', '?')}s]")

            with open(summary_file, "w") as f:
                json.dump(summary, f, indent=2)

    _print_table(summary, "a(x+y) = bz", k, a_max, b_max)
    return summary


def _load_summary(path):
    """Load existing summary for resumability."""
    if path.exists():
        with open(path) as f:
            return json.load(f)
    return {}


def _setup_logging(log_file):
    for h in logger.handlers[:]:
        logger.removeHandler(h)
    logger.setLevel(logging.INFO)
    fh = logging.FileHandler(log_file, mode="w")
    fh.setFormatter(logging.Formatter("%(asctime)s %(message)s", datefmt="%H:%M:%S"))
    logger.addHandler(fh)
    ch = logging.StreamHandler()
    ch.setFormatter(logging.Formatter("%(message)s"))
    logger.addHandler(ch)


def _print_table(summary, family_name, k, a_max, b_max):
    """Print a formatted table of results."""
    print(f"\n{'=' * 70}")
    print(f"R_{k} Table for {family_name}")
    print(f"{'=' * 70}")

    # Header
    header = f"{'a\\b':>6}"
    for b in range(1, b_max + 1):
        header += f"{b:>8}"
    print(header)
    print("-" * (6 + 8 * b_max))

    for a in range(1, a_max + 1):
        row = f"{a:>6}"
        for b in range(1, b_max + 1):
            key = f"({a},{b})"
            if key in summary and summary[key]["status"] == "solved":
                row += f"{summary[key]['result']:>8}"
            elif key in summary:
                row += f"{'T/O':>8}"
            else:
                row += f"{'?':>8}"
        print(row)
    print()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Sweep Rado number tables")
    parser.add_argument("--family", type=int, choices=[1, 2], required=True)
    parser.add_argument("--k", type=int, default=4, help="Number of colors")
    parser.add_argument("--a-max", type=int, default=10)
    parser.add_argument("--b-max", type=int, default=10)
    parser.add_argument("--max-n", type=int, default=100000)
    parser.add_argument("--timeout", type=int, default=3600, help="Per-instance timeout (s)")
    args = parser.parse_args()

    if args.family == 1:
        sweep_family1(args.k, args.a_max, args.b_max, args.max_n, args.timeout)
    else:
        sweep_family2(args.k, args.a_max, args.b_max, args.max_n, args.timeout)
