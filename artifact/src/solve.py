#!/usr/bin/env python3
"""
solve.py — run a SAT solver on an encoded SRG instance.

Usage:
  python3 solve.py instance.cnf                  # solve to completion
  python3 solve.py instance.cnf --confs 100000   # bounded probe (may return UNKNOWN)

On SAT, decodes the model back to an adjacency matrix using the .map.json
produced by encode.py and writes it to <instance>.solution.json.
Exit codes: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN (budget exhausted).
"""

import argparse
import json
import sys
import time

from pysat.formula import CNF
from pysat.solvers import Solver

PREFERRED = ['cadical195', 'cadical153', 'glucose42', 'glucose3', 'minisat22']
BUDGETABLE = ['glucose42', 'glucose3', 'minisat22']   # support conf budgets
PROOF_CAPABLE = ['glucose42', 'glucose3', 'lingeling']  # cadical via PySAT
                                                        # yields EMPTY proofs
                                                        # (checked 2026-08-06)
                                                        # -- do not use


def pick_solver(budgeted):
    for name in (BUDGETABLE if budgeted else PREFERRED):
        try:
            s = Solver(name=name)
            s.delete()
            return name
        except Exception:
            continue
    raise RuntimeError('no usable SAT solver found')


def decode(model, map_path, v):
    with open(map_path) as f:
        meta = json.load(f)
    pos = {lit for lit in model if lit > 0}
    A = [[0] * v for _ in range(v)]
    for key, val in meta['fixed'].items():
        i, j = map(int, key.split(','))
        A[i][j] = A[j][i] = int(val)
    for key, var in meta['evar'].items():
        i, j = map(int, key.split(','))
        A[i][j] = A[j][i] = int(var in pos)
    return A, meta['params']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cnf')
    ap.add_argument('--confs', type=int, default=None,
                    help='conflict budget for a bounded probe')
    ap.add_argument('--solver', default=None)
    ap.add_argument('--proof', default=None, metavar='PATH',
                    help='write a DRAT proof here on UNSAT (forces a '
                         'proof-capable solver; check with drat-trim)')
    args = ap.parse_args()

    if args.proof:
        name = args.solver or PROOF_CAPABLE[0]
        assert name in PROOF_CAPABLE, \
            f'--proof needs one of {PROOF_CAPABLE} (cadical via PySAT emits empty proofs)'
    else:
        name = args.solver or pick_solver(budgeted=args.confs is not None)
    formula = CNF(from_file=args.cnf)
    print(f'solver={name}  vars={formula.nv}  clauses={len(formula.clauses)}')

    t0 = time.time()
    with Solver(name=name, bootstrap_with=formula,
                with_proof=bool(args.proof)) as s:
        if args.confs is not None:
            s.conf_budget(args.confs)
            res = s.solve_limited()
        else:
            res = s.solve()
        dt = time.time() - t0

        if res is True:
            print(f'SAT in {dt:.2f}s')
            map_path = args.cnf.replace('.cnf', '.map.json')
            try:
                with open(map_path) as f:
                    v = json.load(f)['params'][0]
                A, params = decode(s.get_model(), map_path, v)
                out = args.cnf.replace('.cnf', '.solution.json')
                with open(out, 'w') as f:
                    json.dump({'params': params, 'adjacency': A}, f)
                print(f'model decoded -> {out}')
            except FileNotFoundError:
                print('(no .map.json found; raw model not decoded)')
            sys.exit(10)
        elif res is False:
            print(f'UNSAT in {dt:.2f}s')
            if args.proof:
                with open(args.proof, 'w') as f:
                    f.write('\n'.join(s.get_proof()) + '\n')
                print(f'DRAT proof -> {args.proof} (unchecked; run drat-trim)')
            sys.exit(20)
        else:
            print(f'UNKNOWN after {dt:.2f}s (conflict budget exhausted)')
            sys.exit(0)


if __name__ == '__main__':
    main()
