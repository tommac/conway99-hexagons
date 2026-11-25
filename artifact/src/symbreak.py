#!/usr/bin/env python3
"""
symbreak.py — append lex-leader symmetry-breaking clauses to a Conway-99
skeleton instance (roadmap item 1).

Reads <stem>.cnf + <stem>.map.json produced by
    encode.py 99 14 1 2 --conway-skeleton -o <stem>
and writes:
    <out>.cnf       original clauses + lex-leader clauses
    <out>.map.json  copied verbatim, so solve.py can decode models
    <out>.sb.json   the exact configuration, for the lab notebook

Soundness: see symmetry.py's docstring and test_symmetry.py.  The added
constraints only remove assignments that are residual-group relabelings of
surviving ones; the SAT/UNSAT status of the instance is unchanged.

Usage:
  python3 symbreak.py cnf/conway99_skel -o cnf/conway99_skel_sbA
  python3 symbreak.py cnf/conway99_skel -o cnf/conway99_skel_sbB \
      --random 250 --prefix-random 1024 --seed 42
"""

import argparse
import json
import shutil

import symmetry


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('stem', help='skeleton instance stem (with or without .cnf)')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--no-structured', action='store_true',
                    help='skip the 91 structured elements')
    ap.add_argument('--random', type=int, default=0,
                    help='additionally break on N uniform random group elements')
    ap.add_argument('--seed', type=int, default=42)
    ap.add_argument('--prefix-structured', type=int, default=None,
                    help='lex prefix length for structured elements (default: full)')
    ap.add_argument('--prefix-random', type=int, default=1024,
                    help='lex prefix length for random elements')
    ap.add_argument('--stab1-random', type=int, default=0,
                    help='additionally break on N random pair-1-stabilizer '
                         'elements (canonicalizes the S1-matching cube space)')
    ap.add_argument('--stab1-seed', type=int, default=7)
    ap.add_argument('--prefix-stab1', type=int, default=1024,
                    help='lex prefix for stabilizer elements (1024 covers all '
                         'S1-internal edge positions, max index 785)')
    args = ap.parse_args()

    stem = args.stem[:-4] if args.stem.endswith('.cnf') else args.stem
    out = args.out[:-4] if args.out.endswith('.cnf') else args.out

    with open(stem + '.map.json') as f:
        meta = json.load(f)
    assert meta['skeleton'], 'symmetry breaking is defined for the skeleton instance'
    assert meta.get('sb_order', 'canonical') == 'canonical', \
        'instance already carries lex clauses under a non-canonical order; ' \
        'adding canonical-order clauses would MIX orders (unsound)'

    # cross-check the encoder's outside labeling against symmetry.py's frame
    labels = symmetry.outside_labels()
    pair_of = {int(k): tuple(v) for k, v in meta['pair_of'].items()}
    assert len(pair_of) == 84
    for i, lab in enumerate(labels):
        assert pair_of[15 + i] == lab, 'label order mismatch: encoder vs symmetry.py'

    evar = {}
    for key, var in meta['evar'].items():
        i, j = map(int, key.split(','))
        evar[(i, j)] = var
    pos = symmetry.edge_positions()
    assert len(evar) == len(pos) == 3486
    xvars = [evar[(15 + u, 15 + v)] for u, v in pos]

    elements = []                              # (element, prefix)
    if not args.no_structured:
        for el in symmetry.structured_elements():
            elements.append((el, args.prefix_structured))
    if args.random:
        already = {el for el, _ in elements}
        for el in symmetry.random_elements(args.random, args.seed):
            if el not in already:
                elements.append((el, args.prefix_random))
    if args.stab1_random:
        already = {el for el, _ in elements}
        for el in symmetry.stab1_random_elements(args.stab1_random,
                                                 args.stab1_seed):
            if el not in already:
                elements.append((el, args.prefix_stab1))

    with open(stem + '.cnf') as f:
        header = f.readline().split()
    assert header[:2] == ['p', 'cnf'], 'unexpected DIMACS header'
    nv, ncl = int(header[2]), int(header[3])

    next_aux = nv + 1
    sb_clauses = []
    for (pi, signs), prefix in elements:
        P = symmetry.element_edge_perm(pi, signs)
        cls, next_aux = symmetry.lex_leader_clauses(xvars, P, next_aux, prefix)
        sb_clauses.extend(cls)

    new_nv = next_aux - 1
    new_ncl = ncl + len(sb_clauses)

    with open(stem + '.cnf') as fin, open(out + '.cnf', 'w') as fout:
        fin.readline()                         # drop the old header
        fout.write('p cnf %d %d\n' % (new_nv, new_ncl))
        shutil.copyfileobj(fin, fout, 1 << 20)
        for cl in sb_clauses:
            fout.write(' '.join(map(str, cl)) + ' 0\n')

    shutil.copyfile(stem + '.map.json', out + '.map.json')

    cfg = {
        'base': stem + '.cnf',
        'structured': not args.no_structured,
        'n_structured': 0 if args.no_structured else len(symmetry.structured_elements()),
        'prefix_structured': args.prefix_structured,
        'n_random': args.random,
        'prefix_random': args.prefix_random if args.random else None,
        'seed': args.seed if args.random else None,
        'n_stab1': args.stab1_random,
        'prefix_stab1': args.prefix_stab1 if args.stab1_random else None,
        'stab1_seed': args.stab1_seed if args.stab1_random else None,
        'n_elements': len(elements),
        'sb_clauses': len(sb_clauses),
        'aux_vars': new_nv - nv,
        'total_vars': new_nv,
        'total_clauses': new_ncl,
    }
    with open(out + '.sb.json', 'w') as f:
        json.dump(cfg, f, indent=1)

    print('wrote %s.cnf: +%d lex clauses, +%d aux vars over %d group elements '
          '-> %d vars, %d clauses'
          % (out, len(sb_clauses), new_nv - nv, len(elements), new_nv, new_ncl))


if __name__ == '__main__':
    main()
