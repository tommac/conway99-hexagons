# Code, certificates and Lean sources

This folder supports the paper *If Conway's 99-graph exists, it has at least 209,781 induced
hexagons*. It lets you regenerate every SAT instance behind the paper, check every proof,
and rebuild the Lean development.

| Path | Contents |
|---|---|
| `src/encode.py` | Writes the instance: the rooted strongly regular conditions as CNF |
| `src/symmetry.py`, `src/symbreak.py` | The group S₂ ≀ S₇ acting on the 3,486 variables, and the lex-leader clauses |
| `scripts/graded_canonical.py` | The canonical positions, the counter for "D ≥ d", and the instance generator |
| `src/solve.py` | Glucose 4.2 through `python-sat`, with DRAT proof output |
| `src/sanity.py`, `src/test_symmetry.py`, `src/verify.py`, `src/crosscheck_lean.py` | Tests of the encoder, the symmetry machinery and the Lean cross-check |
| `lean/` | The Lean 4 development (toolchain and Mathlib pinned by `lean-toolchain` and `lake-manifest.json`) |
| `ledgers/certified.jsonl` | One line per certified rung, with SHA-256 digests of the instance and proofs and the checkers' verdicts |

## Requirements

- Python 3 with `pip install -r requirements.txt` (`python-sat` 1.9.dev7)
- [`drat-trim`](https://github.com/marijnheule/drat-trim) at commit `2e3b2dc0`, which also provides `lrat-check`
- [`cake_lpr`](https://github.com/tanyongkiam/cake_lpr) at commit `a36874a8`
- [CaDiCaL](https://github.com/arminbiere/cadical) 3.0.1, for the rungs D ≥ 76 and D ≥ 75
- Lean 4.32.2, through `elan`, for the Lean development

## Regenerate the instances and check the proofs

From this folder:

```bash
mkdir -p cnf
python3 src/encode.py 99 14 1 2 --conway-skeleton -o cnf/conway99_skel
PYTHONPATH=src python3 scripts/graded_canonical.py sbcanon -o cnf/conway99_skel_sbCF

# D >= 77 (and likewise D >= 78): Glucose with DRAT, then both checkers
PYTHONPATH=src python3 scripts/graded_canonical.py gen --dmin 77 --base cnf/conway99_skel_sbCF -o cnf/d77
python3 src/solve.py cnf/d77.cnf --proof cnf/d77.drat --confs 4000000
drat-trim cnf/d77.cnf cnf/d77.drat -L cnf/d77.lrat
cake_lpr cnf/d77.cnf cnf/d77.lrat

# D >= 75, the rung behind the paper: CaDiCaL with LRAT (about an hour, 13.6 GB of proof)
# (D >= 76 the same way, with --dmin 76)
PYTHONPATH=src python3 scripts/graded_canonical.py gen --dmin 75 --base cnf/conway99_skel_sbCF -o cnf/d75
cadical --lrat=true --binary=false cnf/d75.cnf cnf/d75.lrat
cake_lpr cnf/d75.cnf cnf/d75.lrat
lrat-check cnf/d75.cnf cnf/d75.lrat
```

To avoid storing the 13.6 GB proof, write it to a named pipe that the checker reads
(`mkfifo p; cake_lpr cnf/d75.cnf p & cadical --lrat=true --binary=false cnf/d75.cnf p`),
and use `tee` to feed both checkers and `shasum -a 256` at once.

The expected digests are in `ledgers/certified.jsonl`. The instances, and the Glucose DRAT
proofs with their LRAT conversions, were regenerated on 2026-11-25 and agree byte for
byte with the ledger. For D ≥ 75 the instance digest is
`41a769206eb067b42534c9402a5b01f4af61f4c0dd181242519d59086efcf598`, and the LRAT stream
written by CaDiCaL had digest
`fdbe2e91b1b8780f1f9e91e2798a6ac68268f676ffc032d833d30973d35c42cb`.

## Tests

```bash
cd src && python3 sanity.py && python3 crosscheck_lean.py && python3 test_symmetry.py && cd ..
mkdir -p cnf
python3 src/encode.py 99 14 1 2 --conway-skeleton -o cnf/conway99_skel
python3 src/symbreak.py cnf/conway99_skel -o cnf/conway99_skel_sbA
PYTHONPATH=src python3 scripts/graded_canonical.py verify --full-group
PYTHONPATH=src python3 scripts/graded_canonical.py cardtest
```

`sanity.py` runs the encoder on five parameter sets for which strongly regular graphs exist,
and on one for which none does. `crosscheck_lean.py` compares the group tables used by the
encoder with `lean/frame_export.txt`, which Lean computes from its proved definitions.
`test_symmetry.py` checks the lex-leader machinery exhaustively on small cases.
`graded_canonical.py verify --full-group` checks that the canonical positions are invariant
under all 645,120 group elements. `graded_canonical.py cardtest` checks the counter for
"D ≥ d".

## Lean

```bash
cd lean && lake build
```

The build prints the axioms of every headline theorem: only `propext`, `Classical.choice`
and `Quot.sound`. The only exception is a fenced LRAT pilot at the end of
`Conway99/Audit.lean`, which also uses `native_decide`. See `lean/README.md` for what is
proved. That file was written for the rung D ≤ 77: Lean derives n₃ ≥ 348 from it. The paper's
rung D ≤ 74 uses the same arithmetic, done by hand in the paper.

## What is machine-checked, and what is only tested

- **Proved in Lean:** the rooted reduction; the group action, and the soundness of lex-leader
  constraints as an abstract theorem; the flag-counting identity; and the arithmetic from a
  bound on D(x) to the bounds on n₁ and n₃.
- **Checked by proof checkers:** that each instance, as a file, is unsatisfiable.
- **Tested, not proved:** that the CNF file expresses the mathematics. This covers the
  clauses of the encoder, the counter, the lex-leader clauses, and the invariance of the
  strongly regular conditions under the group.
