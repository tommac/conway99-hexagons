#!/usr/bin/env python3
"""
certify.py — certified-UNSAT pipeline (roadmap 2).

Runs: solve.py --proof (glucose42 DRAT tracing) on an encoded instance,
then checks the proof with drat-trim (tools/drat-trim, built from
github.com/marijnheule/drat-trim).  Only a drat-trim "s VERIFIED" counts
as a certified UNSAT — ground rule 2.

Usage:
  python3 certify.py cnf/srg_6_3_0_2.cnf          # solve + certify
  python3 certify.py cnf/foo.cnf --confs 1000000  # budgeted (UNKNOWN possible)

Exit codes: 0 = certified UNSAT, 10 = SAT (no proof applicable),
3 = UNKNOWN (budget), 1 = failure (incl. proof that does NOT verify —
treat as loudly as a bug).
"""

import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent
DRAT_TRIM = HERE.parent / 'tools' / 'drat-trim' / 'drat-trim'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cnf')
    ap.add_argument('--confs', type=int, default=None)
    args = ap.parse_args()

    if not DRAT_TRIM.exists():
        print('FAIL: tools/drat-trim/drat-trim not built '
              '(git clone https://github.com/marijnheule/drat-trim tools/drat-trim && make)')
        sys.exit(1)

    proof = args.cnf.replace('.cnf', '.drat')
    cmd = [sys.executable, str(HERE / 'solve.py'), args.cnf, '--proof', proof]
    if args.confs is not None:
        cmd += ['--confs', str(args.confs)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    sys.stdout.write(r.stdout)
    if r.returncode == 10:
        print('SAT — nothing to certify (verify the model instead).')
        sys.exit(10)
    if r.returncode == 0:
        print('UNKNOWN — budget exhausted, no proof.')
        sys.exit(3)
    if r.returncode != 20:
        print('FAIL: solver error'); sys.stderr.write(r.stderr); sys.exit(1)

    c = subprocess.run([str(DRAT_TRIM), args.cnf, proof],
                       capture_output=True, text=True)
    verified = 's VERIFIED' in c.stdout
    for line in c.stdout.splitlines():
        if line.startswith('s ') or 'resolution' in line or 'proof' in line:
            print('drat-trim:', line)
    if verified:
        print(f'CERTIFIED UNSAT: {args.cnf} (proof {proof} checked by drat-trim)')
        sys.exit(0)
    print('FAIL: drat-trim did NOT verify the proof — do not trust this UNSAT.')
    sys.exit(1)


if __name__ == '__main__':
    main()
