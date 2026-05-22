# Rado Numbers for x + by = bz

Code and data for: **"On Rado Numbers for x + by = bz: The b^k Pattern and a Threshold Conjecture"**

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18957994.svg)](https://doi.org/10.5281/zenodo.18957994)

## Overview

This repository contains the SAT-based computational pipeline for computing multicolor Rado numbers R_k(b) for the equation x + by = bz. The code reproduces all computational results in the paper, including the witness coloring proving R_5(3) > 243.

## Repository Structure

```
├── README.md
├── LICENSE
├── requirements.txt
├── configs/                # Solver configuration
├── src/
│   ├── encoder.py          # SAT encoder for k-color Rado instances
│   ├── solver.py           # Incremental SAT solver (PySAT + CaDiCaL)
│   ├── sweep.py            # Parameter sweep across equation families
│   ├── find_R5_incremental.py  # Incremental search for R_5(3)
│   ├── compression_test.py # Color Compression Lemma verification
│   ├── verify.py           # Verify against known Rado numbers
│   ├── verify_R3_compression.py  # Verify R_3 via compression
│   ├── verify_R4_crosscheck.py   # Cross-check R_4 values
│   ├── verify_R5.py        # Verify R_5(3) > 243
│   ├── verify_R5_witness.py     # Verify witness coloring
│   ├── verify_gstar_tree.py     # Combined-G*-Tree Lemma SAT verification (R_4(3)=81)
│   └── extract_gstar_mus.py     # Unsatisfiable-core / MUS extraction
├── data/
│   ├── known_values/       # Reference values from literature
│   ├── results/            # Computed results and witness colorings
│   └── *.cnf               # DIMACS CNF encodings
└── lean4/                  # Lean 4 + Mathlib formalization
```

## Lean 4 formalization

The [`lean4/`](lean4/) directory contains a Lean 4 + Mathlib
formalization of the multicolor Rado numbers R_k(b) for x + by = bz:
the lower bound, the upper-bound theorems, the independent-verification
theorem, the b^k pattern breakdown, and the statement of the threshold
conjecture. The analytic core is kernel-pure; the SAT-verified results
rest on 5 explicitly declared, SAT-verified axioms. See
[`lean4/README.md`](lean4/README.md) for build instructions and the
axiom audit. The formalization is also the subject of a companion
paper, *A Kernel-Pure Lean 4 Formalization of the Distance Pair
Characterization for the Rado Equation x + by = bz*
([DOI 10.5281/zenodo.20346817](https://doi.org/10.5281/zenodo.20346817)).

## Quick Start

```bash
pip install -r requirements.txt
```

### Verify the witness coloring for R_5(3) > 243

```bash
python src/verify_R5_witness.py
```

### Reproduce the main results table

```bash
python src/sweep.py
```

### Verify against known values

```bash
python src/verify.py
```

## Citation

```bibtex
@misc{li2026rado,
  author       = {Li, Alex Chengyu},
  title        = {On Rado Numbers for $x + by = bz$: The $b^k$ Pattern
                  and a Threshold Conjecture},
  year         = {2026},
  note         = {Preprint, SSRN abstract 6814341},
  howpublished = {\url{https://ssrn.com/abstract=6814341}}
}
```

## License

MIT
