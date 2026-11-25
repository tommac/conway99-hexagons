#!/usr/bin/env python3
"""
encode.py — SAT encoder for strongly regular graph existence: srg(v, k, lambda, mu).

Generic for any parameter set, with an optional canonical "skeleton" for the
Conway-99 problem, srg(99, 14, 1, 2), which fixes (without loss of generality):

  * vertex 0 adjacent to vertices 1..14 (its neighborhood N),
  * the perfect matching induced on N by lambda=1:  {1,2},{3,4},...,{13,14},
  * the 84 outside vertices labeled canonically by the 84 NON-matched pairs
    {a,b} of N: outside vertex x_{a,b} is adjacent to a and b and to nothing
    else in N.  (Every outside vertex has exactly mu=2 neighbors in N — they
    cannot be a matched pair or lambda would be violated — and every
    non-matched pair has exactly one outside common neighbor, so this labeling
    is a pure canonical relabeling: no solutions are lost.)

After the skeleton, the only free variables are the C(84,2) = 3486 adjacencies
among the outside vertices.  All degree/lambda/mu constraints are generated
with full constant propagation against the fixed skeleton.

Variables:
  e(i,j)   : edge between i<j                       (only for non-fixed pairs)
  t(i,j,w) : w is a common neighbor of i and j      (AND of two edge literals)

Constraints:
  * every vertex has degree k                        (cardinality: equals-k)
  * adjacent pairs have exactly lambda common neighbors
  * non-adjacent pairs have exactly mu  common neighbors
    (conditional cardinality, guarded by the pair's edge literal)

Output: DIMACS CNF + a JSON map of edge variables (for decoding/verification).
"""

import argparse
import json
import sys
from itertools import combinations

from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType


def build_skeleton_conway99():
    """Fixed adjacencies for the canonical Conway-99 skeleton.

    Returns dict {(i,j): bool} with i<j, over vertices 0..98.
    Outside vertices 15..98 are labeled by non-matched pairs of {1..14}
    in lexicographic order.
    """
    fixed = {}
    N = list(range(1, 15))                      # neighborhood of vertex 0
    matched = {(1, 2), (3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (13, 14)}

    # vertex 0: adjacent to N, non-adjacent to everything else
    for u in range(1, 99):
        fixed[(0, u)] = (u <= 14)

    # inside N: exactly the matching
    for a, b in combinations(N, 2):
        fixed[(a, b)] = (a, b) in matched

    # outside vertices <-> non-matched pairs (lex order)
    non_matched = [p for p in combinations(N, 2) if p not in matched]
    assert len(non_matched) == 84
    pair_of = {}                                # outside vertex -> its pair
    for idx, (a, b) in enumerate(non_matched):
        x = 15 + idx
        pair_of[x] = (a, b)
        for u in N:
            fixed[(u, x)] = (u == a or u == b)

    # outside-outside pairs are FREE (not in `fixed`)
    return fixed, pair_of


class SRGEncoder:
    def __init__(self, v, k, lam, mu, skeleton=None):
        self.v, self.k, self.lam, self.mu = v, k, lam, mu
        self.fixed = skeleton or {}             # {(i,j): bool}
        self.pool = IDPool()
        self.cnf = CNF()
        self.evar = {}                          # {(i,j): var} for free pairs

    # ---- literal helpers -------------------------------------------------
    def edge_state(self, i, j):
        """Return ('const', bool) or ('lit', var) for pair i<j."""
        if i > j:
            i, j = j, i
        if (i, j) in self.fixed:
            return ('const', self.fixed[(i, j)])
        if (i, j) not in self.evar:
            self.evar[(i, j)] = self.pool.id(('e', i, j))
        return ('lit', self.evar[(i, j)])

    def _equals(self, lits, bound, guard=None):
        """Add: (guard ->) sum(lits) == bound, with constant lits removed."""
        if bound < 0 or bound > len(lits):
            # impossible: assert the guard is false (or UNSAT if no guard)
            self.cnf.append([-guard] if guard else [])
            return
        if not lits:
            return                              # 0 == 0, trivially fine
        enc = CardEnc.equals(lits=lits, bound=bound,
                             vpool=self.pool, encoding=EncType.seqcounter)
        for cl in enc.clauses:
            self.cnf.append(cl + [-guard] if guard else cl)

    # ---- constraint generation ------------------------------------------
    def add_degree_constraints(self):
        for i in range(self.v):
            lits, const = [], 0
            for j in range(self.v):
                if j == i:
                    continue
                kind, val = self.edge_state(i, j)
                if kind == 'const':
                    const += int(val)
                else:
                    lits.append(val)
            self._equals(lits, self.k - const)

    def common_neighbor_lits(self, i, j):
        """Literals/constant counting common neighbors of i and j."""
        lits, const = [], 0
        for w in range(self.v):
            if w == i or w == j:
                continue
            k1, v1 = self.edge_state(i, w)
            k2, v2 = self.edge_state(j, w)
            if k1 == 'const' and not v1:
                continue                        # contributes 0
            if k2 == 'const' and not v2:
                continue
            if k1 == 'const' and k2 == 'const':
                const += 1                      # both fixed true
            elif k1 == 'const':                 # v1 true, v2 is a literal
                lits.append(v2)
            elif k2 == 'const':                 # v2 true, v1 is a literal
                lits.append(v1)
            else:
                t = self.pool.id(('t', i, j, w))
                self.cnf.append([-t, v1])
                self.cnf.append([-t, v2])
                self.cnf.append([t, -v1, -v2])
                lits.append(t)
        return lits, const

    def add_pair_constraints(self):
        for i, j in combinations(range(self.v), 2):
            kind, val = self.edge_state(i, j)
            lits, const = self.common_neighbor_lits(i, j)
            if kind == 'const':
                target = (self.lam if val else self.mu) - const
                self._equals(lits, target)
            else:
                self._equals(lits, self.lam - const, guard=val)
                self._equals(lits, self.mu - const, guard=-val)

    def encode(self):
        self.add_degree_constraints()
        self.add_pair_constraints()
        return self.cnf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('v', type=int)
    ap.add_argument('k', type=int)
    ap.add_argument('lam', type=int)
    ap.add_argument('mu', type=int)
    ap.add_argument('--conway-skeleton', action='store_true',
                    help='apply the canonical srg(99,14,1,2) skeleton')
    ap.add_argument('-o', '--out', default=None, help='output CNF path')
    args = ap.parse_args()

    skeleton, pair_of = None, None
    if args.conway_skeleton:
        assert (args.v, args.k, args.lam, args.mu) == (99, 14, 1, 2), \
            'skeleton is specific to srg(99,14,1,2)'
        skeleton, pair_of = build_skeleton_conway99()

    enc = SRGEncoder(args.v, args.k, args.lam, args.mu, skeleton)
    cnf = enc.encode()

    stem = args.out or f'srg_{args.v}_{args.k}_{args.lam}_{args.mu}' \
        + ('_skel' if args.conway_skeleton else '')
    cnf_path = stem if stem.endswith('.cnf') else stem + '.cnf'
    cnf.to_file(cnf_path)

    meta = {
        'params': [args.v, args.k, args.lam, args.mu],
        'skeleton': bool(args.conway_skeleton),
        'fixed': {f'{i},{j}': val for (i, j), val in (skeleton or {}).items()},
        'evar': {f'{i},{j}': var for (i, j), var in enc.evar.items()},
        'pair_of': {str(x): list(p) for x, p in (pair_of or {}).items()},
    }
    with open(cnf_path.replace('.cnf', '.map.json'), 'w') as f:
        json.dump(meta, f)

    print(f'wrote {cnf_path}: {cnf.nv} vars, {len(cnf.clauses)} clauses '
          f'({len(enc.evar)} free edge vars)')


if __name__ == '__main__':
    main()
