"""Production verification of Lemma 3 (Combined-G*-Tree Lemma) from rado_numbers.tex.

For each target color c in {0,1,2,3}, build the SAT instance over {1,...,80}
for the equation x + 3y = 3z (b=3, k=4), using the project's encoder
(four clause types in Sec 7.1), and add the binary edge-blocking clauses
that forbid every edge of G* from being monochromatically colored c.

G* = G_27 union G_ext, where:
  G_27  = { (y, y + 27)   : y in {1, ..., 53} }   -> 53 Type-A edges
  G_ext = { (3d, 81 - d)  : d in {1, ..., 26} }   -> 26 Type-B edges

Paper claim (rado_numbers.tex:632-644): all four per-color instances are
verified UNSAT by CaDiCaL 1.5.3 in under one second per color.

Emits per-color results to data/results/gstar_tree_verification.json.
"""

import json
import os
import sys
import time

from pysat.solvers import Cadical153

# Allow running directly from the src/ directory
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from encoder import encode_rado_instance, var  # noqa: E402


def build_gstar_edges():
    """Return (g27, gext, gstar) edge lists for G* on {1,...,80}.

    g27  = [(y, y+27)  for y in 1..53]     -> 53 Type-A edges
    gext = [(3d, 81-d) for d in 1..26]     -> 26 Type-B edges
    gstar = g27 + gext                       -> 79 edges total
    """
    g27 = [(y, y + 27) for y in range(1, 54)]
    gext = [(3 * d, 81 - d) for d in range(1, 27)]
    # Sanity checks on cardinalities and disjointness from Prop 2 of the paper
    assert len(g27) == 53, f"|G_27| expected 53, got {len(g27)}"
    assert len(gext) == 26, f"|G_ext| expected 26, got {len(gext)}"
    g27_set = set(frozenset(e) for e in g27)
    gext_set = set(frozenset(e) for e in gext)
    inter = g27_set & gext_set
    assert not inter, f"G_27 cap G_ext expected empty, got {inter}"
    gstar = g27 + gext
    assert len(gstar) == 79, f"|G*| expected 79, got {len(gstar)}"
    # Sanity: vertex set is exactly {1,...,80}
    verts = set()
    for (u, v) in gstar:
        verts.add(u)
        verts.add(v)
    assert verts == set(range(1, 81)), \
        f"V(G*) expected {{1,...,80}}, missing {set(range(1, 81)) - verts}"
    return g27, gext, gstar


def verify_one_color(c, k, n, base_clauses, gstar_edges):
    """Build the SAT instance for color c, run CaDiCaL, return result dict.

    base_clauses: the encoder's four-clause-type CNF for (b=3, k=4, n=80),
                  already computed once and shared across colors.
    gstar_edges:  list of (u, v) edges of G*.
    """
    solver = Cadical153()
    base_clause_count = 0
    for cl in base_clauses:
        solver.add_clause(cl)
        base_clause_count += 1

    # Edge-blocking clauses: for each (u,v) in G*, add ~v_{c,u} OR ~v_{c,v}
    edge_clause_count = 0
    for (u, v) in gstar_edges:
        solver.add_clause([-var(c, u, k), -var(c, v, k)])
        edge_clause_count += 1

    num_clauses = base_clause_count + edge_clause_count
    num_vars = k * n  # = 320

    t0 = time.time()
    sat = solver.solve()
    elapsed = time.time() - t0
    status = "SAT" if sat else "UNSAT"

    # Capture solver statistics if available
    stats = {}
    try:
        accum = solver.accum_stats()
        if isinstance(accum, dict):
            stats = {kk: vv for kk, vv in accum.items()}
    except Exception:  # noqa: BLE001
        pass

    solver.delete()

    return {
        "color": c,
        "status": status,
        "time_s": elapsed,
        "num_vars": num_vars,
        "num_clauses": num_clauses,
        "num_base_clauses": base_clause_count,
        "num_edge_clauses": edge_clause_count,
        "solver_stats": stats,
    }


def main():
    k = 4
    n = 80
    b = 3  # coefficients (1, b, b) -> equation x + 3y = 3z

    print("=" * 70)
    print("Lemma 3 (Combined-G*-Tree Lemma) — production verification")
    print(f"  Equation: x + {b}y = {b}z;  domain {{1,...,{n}}};  k={k} colors")
    print("=" * 70)

    # --- Encode the base instance once and share across colors ---
    base_clauses, num_vars, solutions = encode_rado_instance(
        a=1, b=b, c=b, k=k, n=n, symmetry_breaking=True
    )
    print(f"\nBase encoding (Sec 7.1):")
    print(f"  num_vars     = {num_vars}")
    print(f"  num_clauses  = {len(base_clauses)}")
    print(f"  num_solutions(x + 3y = 3z, 1..80) = {len(solutions)}  (paper: 1729)")

    # --- Build G* ---
    g27, gext, gstar = build_gstar_edges()
    print(f"\nG* edges:")
    print(f"  |G_27|  = {len(g27)}   (Type-A)")
    print(f"  |G_ext| = {len(gext)}  (Type-B)")
    print(f"  |G*|    = {len(gstar)}  (V={n}, E={len(gstar)} = V-1)")

    # --- Verify per color ---
    results = []
    for c in range(k):
        print(f"\n--- Color c = {c} ---")
        r = verify_one_color(c, k, n, base_clauses, gstar)
        results.append(r)
        print(f"  status      : {r['status']}")
        print(f"  time_s      : {r['time_s']:.4f}")
        print(f"  num_vars    : {r['num_vars']}")
        print(f"  num_clauses : {r['num_clauses']} (base={r['num_base_clauses']} + edges={r['num_edge_clauses']})")

    all_unsat = all(r["status"] == "UNSAT" for r in results)
    max_time = max(r["time_s"] for r in results)
    total_time = sum(r["time_s"] for r in results)

    print("\n" + "=" * 70)
    print(f"  All four colors UNSAT     : {all_unsat}")
    print(f"  Max per-color solve time  : {max_time:.4f} s  (paper: < 1.0 s)")
    print(f"  Total solve time          : {total_time:.4f} s")
    print("=" * 70)

    # --- Persist results ---
    out_dir = os.path.normpath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "results")
    )
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "gstar_tree_verification.json")

    payload = {
        "lemma": "Combined-G*-Tree Lemma (Lemma 3)",
        "paper_source": "paper/latex/rado_numbers.tex (lines 532-571, 629-664)",
        "encoding_source": "src/encoder.py (encode_rado_instance)",
        "solver": "CaDiCaL 1.5.3 via pysat.solvers.Cadical153",
        "equation": "x + 3y = 3z",
        "b": b,
        "k": k,
        "n": n,
        "num_vars": num_vars,
        "num_base_clauses": len(base_clauses),
        "num_rado_triples_in_domain": len(solutions),
        "g27_edges": g27,
        "gext_edges": gext,
        "gstar_num_edges": len(gstar),
        "per_color_results": results,
        "all_unsat": all_unsat,
        "max_time_s": max_time,
        "total_time_s": total_time,
        "paper_claim_under_one_second_per_color": True,
        "paper_claim_met": all_unsat and max_time < 1.0,
    }
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)
    print(f"\nResults written to {out_path}")

    # Exit non-zero if not all UNSAT (so the script can be used as a check)
    if not all_unsat:
        sys.exit(2)


if __name__ == "__main__":
    main()
