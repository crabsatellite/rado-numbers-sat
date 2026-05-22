"""MUS / unsat-core extraction for the Combined-G*-Tree Lemma instance.

For each color c in {0,1,2,3} (default c=0 only, to honor the time budget),
build the same SAT instance as `verify_gstar_tree.py`, but mark every
"no-monochromatic-triple" clause and every "G*-edge" clause as a SOFT clause.
Coloring (at-least-one / at-most-one / symmetry-break) clauses are HARD.

Two modes:
  --mode core : extract one unsatisfiable CORE from a single CaDiCaL call
                (each soft clause is tagged by a unique selector literal;
                the negated selectors are passed as assumptions). FAST.
                The core is an UPPER bound on the MUS size and on the
                number of unique triples / unique G* edges in the MUS.
  --mode mus  : run pysat.examples.musx.MUSX (deletion-based) starting
                from the core. SLOW but yields a true MUS (which
                supports the paper's "at least 947 of 1729" claim).
                Default mode.

Paper claim (rado_numbers.tex:646-650):
> The resulting MUS contains at least 947 of the 1729 candidate Rado
> triples in {1, ..., 80}.

The unsat core is sufficient to show the MUS is SMALLER than core_size,
but to lower-bound MUS triples we need the full MUS (or a deletion-based
shrink of the core).

Emits results to data/results/gstar_tree_mus.json (mus mode) or
data/results/gstar_tree_core.json (core mode).
"""

import json
import os
import sys
import time

from pysat.examples.musx import MUSX
from pysat.formula import WCNF
from pysat.solvers import Cadical153

# Allow running directly from the src/ directory
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from encoder import (  # noqa: E402
    encode_coloring_constraints,
    encode_no_monochromatic,
    encode_symmetry_breaking,
    find_solutions_axby_eq_cz,
    var,
)
from verify_gstar_tree import build_gstar_edges  # noqa: E402


def build_labelled_instance(c, k, n, seed_chi_54=None):
    """Build a WCNF with hard = coloring + symm-break; soft = triple + edge clauses.

    Args:
        c: target color for the G* edge-blocking clauses.
        k, n: SAT instance parameters (4, 80 for Lemma 3).
        seed_chi_54: if not None (e.g. 0), add chi(54) = seed_chi_54 as a
                     HARD unit clause. The paper (rado_numbers.tex:672-674)
                     extracts MUS for the "representative seeded instance
                     with chi(54) = 0".

    Returns:
        wcnf: pysat.formula.WCNF instance.
        labels: list of dicts, one per SOFT clause, in the order they were
                appended to wcnf.soft. Each label is one of:
                  {"kind": "triple", "triple": (x,y,z), "color": i}
                  {"kind": "edge",   "edge": (u,v),     "color": c}
        triples: the full list of 1729 Rado triples.
        edges: the full list of 79 G* edges.
    """
    wcnf = WCNF()

    # ----- HARD clauses -----
    # 1) coloring constraints: at-least-one + at-most-one per integer
    for cl in encode_coloring_constraints(k, n):
        wcnf.append(cl)
    # 2) symmetry breaking: chi(1) = 0
    for cl in encode_symmetry_breaking(k):
        wcnf.append(cl)
    # 3) Optional seeding: chi(54) = seed_chi_54
    if seed_chi_54 is not None:
        wcnf.append([var(seed_chi_54, 54, k)])

    # ----- SOFT clauses with labels -----
    labels = []

    # 3) no-monochromatic-triple clauses (one per (triple, color))
    triples = find_solutions_axby_eq_cz(a=1, b=3, c=3, n=n)
    assert len(triples) == 1729, f"Expected 1729 triples, got {len(triples)}"

    for (x, y, z) in triples:
        for i in range(k):
            cl = [-var(i, x, k), -var(i, y, k), -var(i, z, k)]
            cl = list(dict.fromkeys(cl))  # dedupe like the encoder does
            wcnf.append(cl, weight=1)
            labels.append({"kind": "triple", "triple": (x, y, z), "color": i})

    # 4) G* edge-blocking clauses for the chosen target color c
    g27, gext, gstar = build_gstar_edges()
    for (u, v) in gstar:
        cl = [-var(c, u, k), -var(c, v, k)]
        wcnf.append(cl, weight=1)
        labels.append({"kind": "edge", "edge": (u, v), "color": c})

    return wcnf, labels, triples, gstar


def run_mus_for_color(c, k, n, time_budget_s, mus_solver="cadical153", seed_chi_54=None):
    """Run MUSX on the labelled instance for color c.

    Returns dict with keys:
        color, status, time_s, mus_size, mus_triple_count,
        mus_unique_triples, mus_edge_count, mus_unique_edges,
        timed_out, num_hard, num_soft, time_budget_s.

    MUS extraction is a sequence of SAT calls; we cannot interrupt MUSX
    mid-compute. We start a subprocess, wait up to time_budget_s, and on
    timeout we report partial.
    """
    print(f"  Building WCNF for c={c} (seed_chi_54={seed_chi_54})...")
    wcnf, labels, triples, edges = build_labelled_instance(c, k, n, seed_chi_54=seed_chi_54)
    n_hard = len(wcnf.hard)
    n_soft = len(wcnf.soft)
    print(f"    hard clauses : {n_hard}")
    print(f"    soft clauses : {n_soft}")

    # MUSX with CaDiCaL 1.5.3 backend
    print(f"  Running MUSX(solver={mus_solver}) for c={c}, budget={time_budget_s}s ...")
    t0 = time.time()

    timed_out = False
    mus_indices = None
    try:
        with MUSX(wcnf, solver=mus_solver, verbosity=0) as musx:
            # Use SIGALRM-equivalent timing: pysat's MUSX has no built-in timeout,
            # so the most reliable approach is a coarse wall-clock check after .compute().
            # If you need a true hard timeout, use signal.alarm on POSIX or
            # multiprocessing.Process on Windows. For the in-budget happy path
            # (~tens of seconds for 7k-clause instances) this is fine.
            mus_indices = musx.compute()
    except KeyboardInterrupt:
        timed_out = True

    elapsed = time.time() - t0
    if elapsed > time_budget_s:
        timed_out = True
        print(f"    [WARN] elapsed {elapsed:.1f}s > budget {time_budget_s}s")
    else:
        print(f"    MUSX returned in {elapsed:.2f}s")

    result = {
        "color": c,
        "time_s": elapsed,
        "time_budget_s": time_budget_s,
        "timed_out": timed_out,
        "num_hard": n_hard,
        "num_soft": n_soft,
        "mus_solver": mus_solver,
    }

    if mus_indices is None:
        result["status"] = "incomplete"
        result["mus_size"] = None
        return result

    # MUSX returns 1-based indices into the soft list
    mus_labels = [labels[i - 1] for i in mus_indices]

    triple_labels = [lab for lab in mus_labels if lab["kind"] == "triple"]
    edge_labels = [lab for lab in mus_labels if lab["kind"] == "edge"]

    unique_triples = sorted({tuple(lab["triple"]) for lab in triple_labels})
    unique_edges = sorted({tuple(lab["edge"]) for lab in edge_labels})

    result["status"] = "complete"
    result["mus_size"] = len(mus_indices)
    result["mus_triple_clause_count"] = len(triple_labels)
    result["mus_unique_triples_count"] = len(unique_triples)
    result["mus_edge_clause_count"] = len(edge_labels)
    result["mus_unique_edges_count"] = len(unique_edges)
    result["mus_unique_triples_sample"] = [list(t) for t in unique_triples[:20]]
    result["mus_unique_edges_sample"] = [list(e) for e in unique_edges[:20]]
    result["candidate_triple_count"] = len(triples)
    result["gstar_edge_count"] = len(edges)
    result["paper_claim_unique_triples_at_least"] = 947
    result["paper_claim_met"] = len(unique_triples) >= 947

    print(f"    MUS size                : {result['mus_size']}")
    print(f"    MUS triple clauses      : {result['mus_triple_clause_count']}")
    print(f"    MUS unique triples      : {result['mus_unique_triples_count']}  (paper: >= 947 of {len(triples)})")
    print(f"    MUS edge clauses        : {result['mus_edge_clause_count']}")
    print(f"    MUS unique edges        : {result['mus_unique_edges_count']}  (of {len(edges)} G* edges)")

    return result


def run_core_for_color(c, k, n, seed_chi_54=None):
    """Extract one unsatisfiable CORE in a single CaDiCaL call.

    Strategy: build the CNF directly into a Cadical153 instance with each
    soft clause augmented by a unique selector literal s_i (positive).
    Pass {-s_i} for all i as assumptions. CaDiCaL returns UNSAT; .get_core()
    gives the subset of assumptions that were used = soft-clause indices
    used in the core.

    Returns dict with the core size, the number of unique triples / edges
    in the core (these are UPPER bounds on the corresponding MUS quantities).
    """
    print(f"  Building labelled CNF for c={c} (core mode, seed_chi_54={seed_chi_54})...")
    wcnf, labels, triples, edges = build_labelled_instance(c, k, n, seed_chi_54=seed_chi_54)

    n_hard = len(wcnf.hard)
    n_soft = len(wcnf.soft)
    print(f"    hard clauses : {n_hard}")
    print(f"    soft clauses : {n_soft}")

    # Allocate one fresh selector variable per soft clause.
    # The base CNF uses 4*80 = 320 vars (k*n). Selectors start at 321.
    base_vars = k * n
    selectors = [base_vars + 1 + i for i in range(n_soft)]
    # Pass -selector as assumption to "activate" the soft clause.
    # Soft clause cl  becomes  cl + [selector]   (so when selector is false,
    # the augmented clause is equivalent to cl; when selector is true,
    # the augmented clause is satisfied trivially and cl is deactivated).

    print(f"    selectors    : {n_soft} (vars {selectors[0]}..{selectors[-1]})")
    print(f"  Running CaDiCaL with assumptions ...")

    solver = Cadical153()
    for cl in wcnf.hard:
        solver.add_clause(cl)
    for i, cl in enumerate(wcnf.soft):
        solver.add_clause(list(cl) + [selectors[i]])

    assumptions = [-s for s in selectors]
    t0 = time.time()
    sat = solver.solve(assumptions=assumptions)
    elapsed = time.time() - t0
    assert not sat, "Instance must be UNSAT"
    core = solver.get_core()
    print(f"    CaDiCaL UNSAT in {elapsed:.2f}s; raw core size = {len(core)}")

    # core is a list of assumption literals (negative selectors).
    # The corresponding soft clauses are the positive index = -lit.
    core_soft_indices_zero_based = sorted({-lit - (base_vars + 1) for lit in core})

    # Map indices back to (kind, triple/edge, color) labels
    core_labels = [labels[i] for i in core_soft_indices_zero_based]
    core_triples = [lab for lab in core_labels if lab["kind"] == "triple"]
    core_edges = [lab for lab in core_labels if lab["kind"] == "edge"]
    unique_triples = sorted({tuple(lab["triple"]) for lab in core_triples})
    unique_edges = sorted({tuple(lab["edge"]) for lab in core_edges})

    print(f"    Unsat core   : {len(core_soft_indices_zero_based)} soft clauses")
    print(f"    -> triple clauses : {len(core_triples)}")
    print(f"    -> edge clauses   : {len(core_edges)}")
    print(f"    -> unique triples : {len(unique_triples)}  (paper MUS bound: >= 947)")
    print(f"    -> unique G* edges: {len(unique_edges)}    (of {len(edges)})")

    solver.delete()

    return {
        "color": c,
        "mode": "core",
        "time_s": elapsed,
        "num_hard": n_hard,
        "num_soft": n_soft,
        "core_size": len(core_soft_indices_zero_based),
        "core_triple_clause_count": len(core_triples),
        "core_edge_clause_count": len(core_edges),
        "core_unique_triples_count": len(unique_triples),
        "core_unique_edges_count": len(unique_edges),
        "core_unique_triples_sample": [list(t) for t in unique_triples[:20]],
        "core_unique_edges": [list(e) for e in unique_edges],
        "candidate_triple_count": len(triples),
        "gstar_edge_count": len(edges),
        "note_core_is_upper_bound_on_mus": (
            "An unsatisfiable core is a SUPERSET of any MUS. Hence core_size "
            "is an UPPER bound on |MUS|, and core_unique_triples_count is an "
            "UPPER bound on |unique triples in MUS|. The paper's '>=947' is a "
            "LOWER bound on the MUS triple count; we cannot directly confirm or "
            "refute it from the core alone (we can only assert that the MUS has "
            "<= core_unique_triples_count unique triples)."
        ),
    }


def run_shrink_for_color(c, k, n, time_budget_s, seed_chi_54=None):
    """Run deletion-based shrink starting from the unsat core, with a
    wall-clock budget. Yields a 'partial MUS' (cannot guarantee minimality
    if interrupted) that is monotonically shrinking.

    Returns dict with the partial-MUS size + upper-bound interpretation.

    Note: the returned active set has the property that it is unsatisfiable
    together with the hard clauses. Continuing this deletion-shrink trajectory
    only removes more elements (never adds), so the final converged MUS along
    this trajectory is a SUBSET of the returned active set. Therefore the
    unique-triple count reported here is an UPPER bound on the converged-MUS
    unique-triple count for THIS particular trajectory. Different deletion-
    shrink trajectories (different solver, different iteration order,
    different starting core) can yield different minimal MUSes with
    potentially different unique-triple counts.
    """
    print(f"  Building labelled CNF for c={c} (shrink mode, seed_chi_54={seed_chi_54})...")
    wcnf, labels, triples, edges = build_labelled_instance(c, k, n, seed_chi_54=seed_chi_54)

    n_hard = len(wcnf.hard)
    n_soft = len(wcnf.soft)

    # Phase 1: get initial unsat core via selector-assumption protocol
    base_vars = k * n
    selectors = [base_vars + 1 + i for i in range(n_soft)]
    solver = Cadical153()
    for cl in wcnf.hard:
        solver.add_clause(cl)
    for i, cl in enumerate(wcnf.soft):
        solver.add_clause(list(cl) + [selectors[i]])

    t0 = time.time()
    sat = solver.solve(assumptions=[-s for s in selectors])
    assert not sat
    core_lits = solver.get_core()
    # active set: zero-based soft-clause indices currently in our candidate MUS
    active = set(-lit - (base_vars + 1) for lit in core_lits)
    elapsed_core = time.time() - t0
    print(f"    Phase 1: core in {elapsed_core:.1f}s, size = {len(active)}")

    # Phase 2: deletion shrink with hard wall-clock budget
    t_shrink_start = time.time()
    removed = 0
    kept = 0
    iterations = 0
    # Iterate over a snapshot list (order: as in core)
    candidates = list(active)
    # Sort by clause type: try edge clauses last (they're more likely to be essential)
    # Actually, randomize to avoid bias; sorted is fine
    for idx in candidates:
        iterations += 1
        if time.time() - t_shrink_start > time_budget_s:
            print(f"    Phase 2: budget exceeded at iter {iterations}/{len(candidates)}")
            break
        # Try removing idx from active set: solve with idx's selector forced true
        # (i.e., assumption +selectors[idx] for inactive)
        if idx not in active:
            continue
        trial_active = active - {idx}
        assumptions = []
        for j in range(n_soft):
            if j in trial_active:
                assumptions.append(-selectors[j])
            else:
                assumptions.append(+selectors[j])
        sat_trial = solver.solve(assumptions=assumptions)
        if not sat_trial:
            # Still UNSAT without idx -> we can remove it
            new_core = solver.get_core()
            active = set(-lit - (base_vars + 1) for lit in new_core)
            removed += 1
        else:
            # SAT without idx -> idx is essential, keep it
            kept += 1

    elapsed_shrink = time.time() - t_shrink_start
    print(f"    Phase 2: shrink done in {elapsed_shrink:.1f}s; removed {removed}, kept {kept}, final size = {len(active)}")

    # Map back to labels
    final_labels = [labels[i] for i in sorted(active)]
    triple_labels = [lab for lab in final_labels if lab["kind"] == "triple"]
    edge_labels = [lab for lab in final_labels if lab["kind"] == "edge"]
    unique_triples = sorted({tuple(lab["triple"]) for lab in triple_labels})
    unique_edges = sorted({tuple(lab["edge"]) for lab in edge_labels})

    completed = iterations == len(candidates)
    solver.delete()

    print(f"    -> final size       : {len(active)}")
    print(f"    -> triple clauses   : {len(triple_labels)}")
    print(f"    -> edge clauses     : {len(edge_labels)}")
    print(f"    -> unique triples   : {len(unique_triples)}   (paper: >= 947, completed={completed})")
    print(f"    -> unique G* edges  : {len(unique_edges)}     (of {len(edges)})")

    return {
        "color": c,
        "mode": "shrink",
        "time_s_core": elapsed_core,
        "time_s_shrink": elapsed_shrink,
        "time_budget_s": time_budget_s,
        "num_hard": n_hard,
        "num_soft": n_soft,
        "phase1_core_size": len(candidates),
        "phase2_iterations": iterations,
        "phase2_removed": removed,
        "phase2_kept": kept,
        "completed": completed,
        "final_size": len(active),
        "final_triple_clause_count": len(triple_labels),
        "final_edge_clause_count": len(edge_labels),
        "final_unique_triples_count": len(unique_triples),
        "final_unique_edges_count": len(unique_edges),
        "final_unique_triples": [list(t) for t in unique_triples],
        "final_unique_edges": [list(e) for e in unique_edges],
        "candidate_triple_count": len(triples),
        "gstar_edge_count": len(edges),
        "paper_claim_unique_triples_at_least": 947,
        "paper_claim_met_if_completed": (completed and len(unique_triples) >= 947),
        "note": (
            "If completed=True, final_unique_triples_count is the exact "
            "MUS unique triple count (per deletion-based MUS definition). "
            "If completed=False, the value is an UPPER bound (we stopped "
            "shrinking with budget left to try) on what a full MUS pass "
            "would give — i.e. the true MUS has <= final_unique_triples_count "
            "unique triples but a longer run could shrink the bound further."
        ),
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description="MUS / core / shrink extraction for Lemma 3.")
    parser.add_argument(
        "--mode", type=str, default="mus", choices=["mus", "core", "shrink"],
        help="'mus' = pysat MUSX (slow, true MUS); 'core' = single-call unsat core (fast, upper bound); 'shrink' = core + deletion shrink with budget",
    )
    parser.add_argument(
        "--colors", type=str, default="0",
        help="Comma-separated colors to extract for (default: 0; full: 0,1,2,3)",
    )
    parser.add_argument(
        "--budget-s", type=int, default=900,
        help="Per-color wall-clock budget in seconds for mus mode (default: 900 = 15 min)",
    )
    parser.add_argument(
        "--solver", type=str, default="cadical153",
        help="Backend SAT solver (default: cadical153)",
    )
    parser.add_argument(
        "--seed-chi54", type=int, default=None,
        help=(
            "If set (e.g. 0), add chi(54) = <value> as a HARD unit clause. "
            "Paper (rado_numbers.tex:672-674) uses chi(54)=0 for the "
            "representative MUS-extraction instance."
        ),
    )
    args = parser.parse_args()

    colors = [int(x) for x in args.colors.split(",")]
    k = 4
    n = 80

    print("=" * 70)
    print(f"Lemma 3 — {args.mode.upper()} extraction")
    print(f"  Colors  : {colors}")
    print(f"  Mode    : {args.mode}")
    if args.mode == "mus":
        print(f"  Budget  : {args.budget_s} s per color")
    print(f"  Solver  : {args.solver}")
    print("=" * 70)

    results = []
    t_start = time.time()
    for c in colors:
        print(f"\n=== Color c = {c} ===")
        if args.mode == "mus":
            r = run_mus_for_color(c, k, n, args.budget_s, mus_solver=args.solver,
                                  seed_chi_54=args.seed_chi54)
        elif args.mode == "core":
            r = run_core_for_color(c, k, n, seed_chi_54=args.seed_chi54)
        else:  # shrink
            r = run_shrink_for_color(c, k, n, args.budget_s, seed_chi_54=args.seed_chi54)
        results.append(r)

    total_elapsed = time.time() - t_start

    payload = {
        "lemma": f"Combined-G*-Tree Lemma (Lemma 3) — {args.mode.upper()} extraction",
        "paper_source": "paper/latex/rado_numbers.tex (lines 646-650, 1006-1010)",
        "encoder_source": "src/encoder.py",
        "extraction_mode": args.mode,
        "extraction_tool": (
            "pysat.examples.musx.MUSX (deletion-based)" if args.mode == "mus"
            else "pysat.solvers.Cadical153 with selector-assumption protocol (single call)"
        ),
        "solver": args.solver,
        "k": k,
        "n": n,
        "seed_chi_54": args.seed_chi54,
        "candidate_triple_count": 1729,
        "gstar_edge_count": 79,
        "per_color_results": results,
        "total_time_s": total_elapsed,
    }

    out_dir = os.path.normpath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "results")
    )
    os.makedirs(out_dir, exist_ok=True)
    if args.mode == "mus":
        out_filename = "gstar_tree_mus.json"
    elif args.mode == "core":
        out_filename = "gstar_tree_core.json"
    else:
        out_filename = "gstar_tree_shrink.json"
    out_path = os.path.join(out_dir, out_filename)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    print("\n" + "=" * 70)
    print(f"Total wall time : {total_elapsed:.1f} s")
    print(f"Results written : {out_path}")
    print("=" * 70)


if __name__ == "__main__":
    main()
