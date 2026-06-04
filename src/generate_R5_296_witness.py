"""Generate a public witness for R_5(3) > 296.


SAT means that there exists a 5-coloring of {1,...,296} with no
monochromatic solution to x + 3y = 3z.  The output is a JSON witness
that is independently checked by ``verify_R5_witness.py``.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from encoder import encode_rado_instance, var
from pysat.formula import CNF
from pysat.solvers import Cadical153


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "results" / "R5_witness_296.json"
SEED = ROOT / "data" / "results" / "R5_witness_243.json"


def extract_coloring(model: list[int], k: int, n: int) -> dict[str, int]:
    positive = {lit for lit in model if lit > 0}
    coloring: dict[str, int] = {}
    for j in range(1, n + 1):
        hits = [c for c in range(k) if var(c, j, k) in positive]
        if len(hits) != 1:
            raise RuntimeError(f"expected exactly one color for {j}, got {hits}")
        coloring[str(j)] = hits[0]
    return coloring


def count_mono_triples(coloring: dict[str, int], b: int, n: int) -> tuple[int, int]:
    triples = 0
    mono = 0
    chi = {int(key): int(value) for key, value in coloring.items()}
    for d in range(1, n // b + 1):
        x = b * d
        for y in range(1, n - d + 1):
            z = y + d
            triples += 1
            if chi[x] == chi[y] == chi[z]:
                mono += 1
    return triples, mono


def main() -> int:
    b = 3
    k = 5
    n = 296
    seed_prefix = 9

    clauses, num_vars, solutions = encode_rado_instance(1, b, b, k, n, symmetry_breaking=True)
    with SEED.open("r", encoding="utf-8") as f:
        seed = {int(key): int(value) for key, value in json.load(f)["coloring"].items()}
    for j in range(1, seed_prefix + 1):
        clauses.append([var(seed[j], j, k)])

    cnf = CNF(from_clauses=clauses)
    solver = Cadical153(bootstrap_with=cnf.clauses)
    solver.conf_budget(2_000_000)
    sat = solver.solve_limited(expect_interrupt=False)
    if sat is None:
        solver.delete()
        raise RuntimeError("conflict budget exhausted before finding an n=296 witness")
    if not sat:
        solver.delete()
        raise RuntimeError("seeded n=296 instance is UNSAT; no lower-bound witness found")

    model = solver.get_model()
    solver.delete()
    if model is None:
        raise RuntimeError("solver returned SAT without a model")

    coloring = extract_coloring(model, k, n)
    triples_checked, mono_triples = count_mono_triples(coloring, b, n)
    counts = Counter(coloring.values())

    result = {
        "n": n,
        "k": k,
        "b": b,
        "valid": mono_triples == 0,
        "claim": "R_5(3) > 296",
        "equation": "x + 3y = 3z",
        "method": "CaDiCaL 1.5.3 via PySAT on the project SAT encoding",
        "source": "src/generate_R5_296_witness.py",
        "cnf_reference": "data/R5_n296.cnf",
        "seed_reference": "data/results/R5_witness_243.json",
        "seed_prefix_fixed": seed_prefix,
        "sat": True,
        "num_vars": num_vars,
        "num_clauses": len(clauses),
        "solutions_encoded": len(solutions),
        "triples_checked": triples_checked,
        "monochromatic_triples": mono_triples,
        "color_sizes": {str(c): counts.get(c, 0) for c in range(k)},
        "coloring": coloring,
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
        f.write("\n")

    print(f"Wrote {OUT}")
    print(f"SAT witness for n={n}: {triples_checked} triples, {mono_triples} monochromatic")
    return 0 if mono_triples == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
