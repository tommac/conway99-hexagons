#!/usr/bin/env python3
"""
sanity.py — end-to-end pipeline tests on parameter sets with KNOWN answers.

SAT cases (graph exists; solver must find it, verifier must confirm it):
  srg(5,2,0,1)    the 5-cycle (pentagon)
  srg(9,4,1,2)    Paley(9) / 3x3 rook's graph
  srg(10,3,0,1)   the Petersen graph
  srg(13,6,2,3)   Paley(13)
  srg(16,6,2,2)   Shrikhande or 4x4 rook's graph

UNSAT case (no such graph; solver must prove it):
  srg(6,3,0,2)    the only cubic graphs on 6 vertices are K_{3,3} (mu=3)
                  and the triangular prism (lambda>0 on some edges)

Run:  python3 sanity.py
"""

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).parent
DEFAULT_CNF_DIR = HERE.parent / 'cnf'

CASES = [
    # (v, k, lam, mu, expect_sat)
    (5, 2, 0, 1, True),
    (9, 4, 1, 2, True),
    (10, 3, 0, 1, True),
    (13, 6, 2, 3, True),
    (16, 6, 2, 2, True),
    (6, 3, 0, 2, False),
]


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        '--cnf-dir',
        type=Path,
        default=DEFAULT_CNF_DIR,
        help='directory for generated CNFs, maps, proofs, and solutions',
    )
    args = ap.parse_args()
    cnf_dir = args.cnf_dir
    cnf_dir.mkdir(parents=True, exist_ok=True)
    failures = 0
    for v, k, lam, mu, expect_sat in CASES:
        stem = str(cnf_dir / f'srg_{v}_{k}_{lam}_{mu}')
        t0 = time.time()
        r = run([sys.executable, str(HERE / 'encode.py'),
                 str(v), str(k), str(lam), str(mu), '-o', stem])
        if r.returncode != 0:
            print(f'ENCODE FAIL srg({v},{k},{lam},{mu}): {r.stderr.strip()}')
            failures += 1
            continue
        r = run([sys.executable, str(HERE / 'solve.py'), stem + '.cnf'])
        sat = (r.returncode == 10)
        unsat = (r.returncode == 20)
        dt = time.time() - t0

        if expect_sat and sat:
            rv = run([sys.executable, str(HERE / 'verify.py'),
                      stem + '.solution.json'])
            ok = rv.returncode == 0
            status = 'PASS (SAT + independently verified)' if ok \
                else 'FAIL (model did not verify!)'
            failures += 0 if ok else 1
        elif (not expect_sat) and unsat:
            status = 'PASS (UNSAT as expected)'
        else:
            status = f'FAIL (got rc={r.returncode}, expected ' \
                     f'{"SAT" if expect_sat else "UNSAT"})'
            failures += 1
        print(f'srg({v},{k},{lam},{mu}): {status}  [{dt:.2f}s]')

    print()
    if failures:
        print(f'{failures} FAILURE(S) — do not trust the pipeline yet.')
        sys.exit(1)
    print('All sanity checks passed. Pipeline is sound on known ground truth.')


if __name__ == '__main__':
    main()
