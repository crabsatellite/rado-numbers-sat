# Rado Numbers for x + by = bz

Public artifacts for **On Rado Numbers for x + by = bz: The b^k Pattern
and a Threshold Conjecture**.

- SSRN: <https://ssrn.com/abstract=6814341>
- Zenodo concept DOI: <https://doi.org/10.5281/zenodo.18957993>
- Current Zenodo record: <https://doi.org/10.5281/zenodo.22654788>

## Contents

- SAT encoder for k-color instances of x + by = bz.
- R_4(3) = 81 Combined-G*-Tree SAT verification artifacts.
- Distance Pair Lemma slab: k=3, b=3..10 and k=4, b=3..5.
- Explicit R_5(3) > 296 witness and verifier. The exact value is not claimed.
- G* core and core-shrink artifacts.
- Lean 4 + Mathlib formalization and axiom audit.

## Attribution and current scope

The values R_4(3) = 81, R_4(4) = 256, and R_4(5) = 625 were
published by Chang, De Loera, and Wesley in
[Rado Numbers and SAT Computations (2022), Table 10](https://arxiv.org/abs/2210.03262).
Their equation a(x-y) = bz, with their b=1, gives this family's
values after a permutation of variables. The additional values 171 and 103
in main_results.json are also previously published values.

The [September 2026 v2.1 manuscript](https://doi.org/10.5281/zenodo.22654788)
already distinguishes these known values from this project's proofs and
independent verification artifacts. On 12 November 2026, the repository's
older NEW flags were synchronized with that attribution. Unresolved cells
are not labelled as new exact values. Numerical witnesses, solver artifacts,
and Lean source are unchanged by this metadata correction.

### Acknowledgement

I thank the [axeyum project](https://github.com/mjbommar/axeyum/blob/650b3bac4f7bcecf673f0fe1f54ef31fbe62b1be/docs/campaign-2026-08-13/agent-c-rado-akb2/RESULT.md)
for identifying the stale novelty flags and explaining their correspondence
with the earlier table.

## Reproduce

```bash
pip install -r requirements.txt

python src/verify_R5_witness.py data/results/R5_witness_296.json
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
data/results/main_results.json
data/results/R5_witness_296.json
data/results/R5_witness_243.json
data/results/dpl_paper_slab_verification.json
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
