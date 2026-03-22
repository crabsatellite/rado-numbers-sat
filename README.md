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
│   └── verify_R5_witness.py     # Verify witness coloring
└── data/
    ├── known_values/       # Reference values from literature
    ├── results/            # Computed results and witness colorings
    └── *.cnf               # DIMACS CNF encodings
```

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
  doi          = {10.5281/zenodo.18957994},
  publisher    = {Zenodo}
}
```

## License

MIT
