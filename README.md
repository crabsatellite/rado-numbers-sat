# Rado Numbers for x + by = bz

Public artifacts for:

**On Rado Numbers for x + by = bz: The b^k Pattern and a Threshold Conjecture**

- SSRN abstract: <https://ssrn.com/abstract=6814341>
- Zenodo concept DOI: <https://doi.org/10.5281/zenodo.18957993>
- Latest Zenodo record checked here: <https://doi.org/10.5281/zenodo.20343697>

## Contents

- SAT encoder for k-color instances of x + by = bz.
- R_4(3) = 81 Combined-G*-Tree SAT verification artifacts.
- Distance Pair Lemma slab: k=3, b=3..10 and k=4, b=3..5.
- Explicit R_5(3) > 243 witness and verifier.
- Incremental SAT evidence and CNF instances for R_5(3) > 296.
- G* core and core-shrink artifacts.
- Lean 4 + Mathlib formalization and axiom audit.

## Reproduce

```bash
pip install -r requirements.txt

python src/verify_R5_witness.py
python src/verify_gstar_tree.py
python src/verify_dpl_paper_slab.py

cd lean4
lake env lean RadoNumbers/AxiomAudit.lean
```

The DPL slab includes the largest checked case b=5, k=4 and can take
substantial CPU time. The checked manifest is included at
`data/results/dpl_paper_slab_verification.json`.

## Key Files

```text
src/encoder.py
src/verify_gstar_tree.py
src/verify_dpl_paper_slab.py
src/verify_R5_witness.py
src/find_R5_incremental.py
data/results/main_results.json
data/results/R5_witness_243.json
data/results/dpl_paper_slab_verification.json
data/R5_n296.cnf
data/R5_n297.cnf
lean4/RadoNumbers/AxiomAudit.lean
```

## Citation

```bibtex
@misc{li2026rado,
  author       = {Li, Alex Chengyu},
  title        = {On Rado Numbers for $x + by = bz$: The $b^k$ Pattern
                  and a Threshold Conjecture},
  year         = {2026},
  note         = {Preprint, SSRN abstract 6814341},
  howpublished = {\url{https://ssrn.com/abstract=6814341}},
  doi          = {10.5281/zenodo.18957993}
}
```

## License

MIT
