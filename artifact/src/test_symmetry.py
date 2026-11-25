#!/usr/bin/env python3
"""
test_symmetry.py — verification battery for symmetry.py.  Ground rule 1
applies to machinery, not just models: nothing from symmetry.py touches a
real instance until every test here passes.

  T1  group sanity: structured set has 91 distinct elements; at npairs=2
      the full group (8 elements) is generated, distinct, and closed;
      induced label/edge maps are bijections that respect composition and
      inverses.
  T2  direct relabeling, the decisive test: for random group elements g
      and random outside assignments X on the REAL 99-vertex skeleton,
      relabeling the full graph by g's vertex permutation (a) preserves
      the skeleton exactly, (b) carries the outside-edge vector X to
      exactly X o P_g^{-1} where P_g is symmetry.edge_perm's output — so
      the lex constraints talk about genuine graph relabelings — and
      (c) preserves the multiset of degrees and common-neighbor counts
      (the SRG constraint profile is relabel-invariant, checked on
      arbitrary infeasible assignments where the profile is rich).
  T3  lex encoding, exhaustive: the X<=Y encoding agrees with Python
      tuple comparison on ALL assignments for n=1..4; the X <= X o P
      wrapper agrees on all 2^6 assignments for a dozen random P, with
      and without prefix truncation.
  T4  Paley(9) ground truth (general encoder, no skeleton): exactly 5040
      labeled models (= 9!/72, both factors asserted), every one passes
      the independent verifier; lex-leader clauses for a 28-element
      subset of S9 leave EXACTLY the models a pure-Python lex filter
      keeps — nonempty and containing the global lex-minimum.
  T5  skeleton analogue at npairs=2: the hand-built srg(9,4,1,2) skeleton
      instance has EXACTLY ONE model (counting argument: the 9*8 = 72
      skeleton-labelings of the unique srg(9,4,1,2) form a single free
      orbit of its 72-element automorphism group), the model verifies, it
      is invariant under the full order-8 residual group S2 wr S2, and
      full lex-leader over all 7 non-identity elements keeps exactly it.

Run:  python3 test_symmetry.py
"""

import random
import subprocess
import sys
from collections import Counter
from itertools import combinations, product
from pathlib import Path

from pysat.solvers import Solver

import encode
import symmetry
import verify


def enumerate_models(clauses, xvars, solver='glucose42'):
    """All models projected onto xvars, via blocking clauses."""
    out = set()
    with Solver(name=solver, bootstrap_with=clauses) as s:
        while s.solve():
            pos = set(l for l in s.get_model() if l > 0)
            bits = tuple(int(v in pos) for v in xvars)
            assert bits not in out, 'blocking clause failed'
            out.add(bits)
            s.add_clause([(-v if b else v) for v, b in zip(xvars, bits)])
    return out


# ---- T1 ------------------------------------------------------------------

def t1():
    els = symmetry.structured_elements()
    assert len(els) == 91 and len(set(els)) == 91

    # npairs=2: the full group, exhaustively
    small = [(pi, s) for pi in ((0, 1), (1, 0))
             for s in product((0, 1), repeat=2)]
    maps = [tuple(sorted(symmetry.sigma_on_N(pi, s, 2).items()))
            for pi, s in small]
    assert len(set(maps)) == 8, 'wreath elements not distinct at npairs=2'
    as_dicts = [dict(m) for m in maps]
    closed = {m for m in maps}
    for m1 in as_dicts:
        for m2 in as_dicts:
            comp = tuple(sorted((v, m2[m1[v]]) for v in m1))
            assert comp in closed, 'group not closed at npairs=2'

    # npairs=7: composition and inverses respected by the induced actions
    rng = random.Random(1)
    sample = els + symmetry.random_elements(20, seed=7)
    n_edge = len(symmetry.edge_positions())
    for _ in range(30):
        p1, s1 = sample[rng.randrange(len(sample))]
        p2, s2 = sample[rng.randrange(len(sample))]
        m1 = symmetry.sigma_on_N(p1, s1)
        m2 = symmetry.sigma_on_N(p2, s2)
        comp = {v: m2[m1[v]] for v in m1}
        assert sorted(comp.values()) == list(range(1, 15))
        for a, b in symmetry.matched_pairs():
            x, y = comp[a], comp[b]
            assert abs(x - y) == 1 and min(x, y) % 2 == 1, 'matching broken'
        o1 = symmetry.outside_perm(m1)
        o2 = symmetry.outside_perm(m2)
        oc = symmetry.outside_perm(comp)
        assert oc == [o2[o1[i]] for i in range(84)], 'label action not a homomorphism'
        e1 = symmetry.edge_perm(o1)
        e2 = symmetry.edge_perm(o2)
        ec = symmetry.edge_perm(oc)
        assert ec == [e2[e1[t]] for t in range(n_edge)], 'edge action not a homomorphism'
        minv = {v: k for k, v in m1.items()}
        einv = symmetry.edge_perm(symmetry.outside_perm(minv))
        assert all(einv[e1[t]] == t for t in range(n_edge)), 'inverse not respected'
    print('T1 PASS  group structure, homomorphism, inverses')


# ---- T2 ------------------------------------------------------------------

def _profile(A):
    """(sorted degree list, multiset of (adjacent, #common-neighbors))."""
    n = len(A)
    rows = []
    for i in range(n):
        r = 0
        for j in range(n):
            if A[i][j]:
                r |= 1 << j
        rows.append(r)
    degs = sorted(bin(r).count('1') for r in rows)
    prof = Counter()
    for i in range(n):
        for j in range(i + 1, n):
            mask = ~((1 << i) | (1 << j))
            cn = bin(rows[i] & rows[j] & mask).count('1')
            prof[(A[i][j], cn)] += 1
    return degs, prof


def t2():
    fixed, pair_of = encode.build_skeleton_conway99()
    labels = symmetry.outside_labels()
    for i in range(84):
        assert pair_of[15 + i] == labels[i], 'encoder labels != symmetry frame'
    pos = symmetry.edge_positions()
    rng = random.Random(2)
    els = symmetry.random_elements(12, seed=3) + \
        [symmetry.structured_elements()[i] for i in (0, 6, 7, 10, 33, 88)]
    for n_sample, (pi, s) in enumerate(els):
        X = [rng.randrange(2) for _ in range(len(pos))]
        A = [[0] * 99 for _ in range(99)]
        for (i, j), val in fixed.items():
            A[i][j] = A[j][i] = int(val)
        for t, (u, v) in enumerate(pos):
            A[15 + u][15 + v] = A[15 + v][15 + u] = X[t]

        m14 = symmetry.sigma_on_N(pi, s)
        p99 = {0: 0}
        p99.update(m14)
        operm = symmetry.outside_perm(m14)
        for u in range(84):
            p99[15 + u] = 15 + operm[u]
        assert sorted(p99.values()) == list(range(99))

        A2 = [[0] * 99 for _ in range(99)]
        for i in range(99):
            pi_i = p99[i]
            for j in range(99):
                A2[pi_i][p99[j]] = A[i][j]

        # (a) the relabeled graph carries the skeleton exactly
        for (i, j), val in fixed.items():
            assert A2[i][j] == int(val), 'skeleton not preserved'
        # (b) its outside-edge vector is X o P^{-1} for P = edge_perm(...)
        X2 = [A2[15 + u][15 + v] for (u, v) in pos]
        P = symmetry.edge_perm(operm)
        assert all(X2[P[t]] == X[t] for t in range(len(pos))), \
            'induced edge action does not match graph relabeling'
        # (c) SRG constraint profile is relabel-invariant
        if n_sample < 4:
            assert _profile(A) == _profile(A2), 'constraint profile changed'
    print('T2 PASS  99-vertex relabeling: skeleton preserved, edge action exact, profile invariant')


# ---- T3 ------------------------------------------------------------------

def t3():
    for n in range(1, 5):
        xv = list(range(1, n + 1))
        yv = list(range(n + 1, 2 * n + 1))
        cls, _ = symmetry.lex_le_clauses(xv, yv, 2 * n + 1)
        with Solver(name='glucose42', bootstrap_with=cls) as s:
            for bits in product((0, 1), repeat=2 * n):
                x, y = bits[:n], bits[n:]
                assum = [v if b else -v for v, b in zip(xv + yv, bits)]
                assert s.solve(assumptions=assum) == (x <= y), (x, y)

    rng = random.Random(5)
    n = 6
    xv = list(range(1, n + 1))
    perms = [tuple(rng.sample(range(n), n)) for _ in range(12)] + [tuple(range(n))]
    for Pt in perms:
        for prefix in (None, 3):
            cls, _ = symmetry.lex_leader_clauses(xv, list(Pt), n + 1, prefix)
            with Solver(name='glucose42', bootstrap_with=cls) as s:
                for bits in product((0, 1), repeat=n):
                    L = n if prefix is None else prefix
                    ref = tuple(bits[t] for t in range(L)) <= \
                        tuple(bits[Pt[t]] for t in range(L))
                    assum = [v if b else -v for v, b in zip(xv, bits)]
                    assert s.solve(assumptions=assum) == ref, (bits, Pt, prefix)

    # arbitrary comparison orders (campaign --sb-order), alone AND
    # combined with prefix truncation: exhaustive at n=6
    for Pt in perms[:6]:
        order = rng.sample(range(n), n)
        for prefix in (None, 3):
            cls, _ = symmetry.lex_leader_clauses(xv, list(Pt), n + 1,
                                                 prefix=prefix, order=order)
            with Solver(name='glucose42', bootstrap_with=cls) as s:
                for bits in product((0, 1), repeat=n):
                    win = order if prefix is None else order[:prefix]
                    ref = tuple(bits[t] for t in win) <= \
                        tuple(bits[Pt[t]] for t in win)
                    assum = [v if b else -v for v, b in zip(xv, bits)]
                    assert s.solve(assumptions=assum) == ref, \
                        (bits, Pt, order, prefix)
    print('T3 PASS  lex encoding exhaustively correct (independent XY; X vs X.P; '
          'prefixes; arbitrary orders)')


# ---- T4 ------------------------------------------------------------------

def t4():
    enc = encode.SRGEncoder(9, 4, 1, 2)
    cnf = enc.encode()
    pairs9 = list(combinations(range(9), 2))
    xv = [enc.evar[p] for p in pairs9]
    eidx9 = {p: t for t, p in enumerate(pairs9)}

    models = enumerate_models(cnf.clauses, xv)
    assert len(models) == 5040, len(models)
    assert 362880 % len(models) == 0 and 362880 // len(models) == 72

    for m in models:
        A = [[0] * 9 for _ in range(9)]
        for t, (i, j) in enumerate(pairs9):
            A[i][j] = A[j][i] = m[t]
        assert verify.verify([9, 4, 1, 2], A) == [], 'enumerated model failed verifier'

    rng = random.Random(11)
    g_els = [tuple(range(i)) + (i + 1, i) + tuple(range(i + 2, 9))
             for i in range(8)]
    g_els += [tuple(rng.sample(range(9), 9)) for _ in range(20)]
    Ps = []
    for g in g_els:
        P = []
        for i, j in pairs9:
            x, y = g[i], g[j]
            if x > y:
                x, y = y, x
            P.append(eidx9[(x, y)])
        Ps.append(P)

    all_cls = list(cnf.clauses)
    next_aux = cnf.nv + 1
    for P in Ps:
        cls, next_aux = symmetry.lex_leader_clauses(xv, P, next_aux)
        all_cls.extend(cls)
    W = enumerate_models(all_cls, xv)
    W_ref = {m for m in models
             if all(m <= tuple(m[P[t]] for t in range(len(P))) for P in Ps)}
    assert W == W_ref, 'CNF lex filter != pure-Python lex filter'
    assert W and min(models) in W
    print('T4 PASS  Paley(9): 5040 models all verified; 28-element lex-leader '
          'keeps exactly the Python-filtered %d models (incl. global min)' % len(W))
    return len(W)


# ---- T5 ------------------------------------------------------------------

def _skeleton_srg9():
    fixed = {}
    N = [1, 2, 3, 4]
    matched = {(1, 2), (3, 4)}
    for u in range(1, 9):
        fixed[(0, u)] = (u <= 4)
    for a, b in combinations(N, 2):
        fixed[(a, b)] = (a, b) in matched
    for i, (a, b) in enumerate(symmetry.outside_labels(2)):
        x = 5 + i
        for u in N:
            fixed[(u, x)] = (u == a or u == b)
    return fixed


def t5():
    fixed = _skeleton_srg9()
    enc = encode.SRGEncoder(9, 4, 1, 2, skeleton=fixed)
    cnf = enc.encode()
    pos = symmetry.edge_positions(2)
    xv = [enc.evar[(5 + u, 5 + v)] for u, v in pos]

    models = enumerate_models(cnf.clauses, xv)
    assert len(models) == 1, models
    (m,) = models
    A = [[0] * 9 for _ in range(9)]
    for (i, j), val in fixed.items():
        A[i][j] = A[j][i] = int(val)
    for t, (u, v) in enumerate(pos):
        A[5 + u][5 + v] = A[5 + v][5 + u] = m[t]
    assert verify.verify([9, 4, 1, 2], A) == []

    group = [(pi, s) for pi in ((0, 1), (1, 0))
             for s in product((0, 1), repeat=2)]
    for pi, s in group:
        P = symmetry.element_edge_perm(pi, s, 2)
        assert tuple(m[P[t]] for t in range(6)) == m, \
            'unique model not invariant under residual group'

    all_cls = list(cnf.clauses)
    next_aux = cnf.nv + 1
    for pi, s in group:
        if pi == (0, 1) and s == (0, 0):
            continue
        P = symmetry.element_edge_perm(pi, s, 2)
        cls, next_aux = symmetry.lex_leader_clauses(xv, P, next_aux)
        all_cls.extend(cls)
    W = enumerate_models(all_cls, xv)
    assert W == models, 'full lex-leader must keep exactly the unique model'
    print('T5 PASS  npairs=2 skeleton: unique model (as counted), verified, '
          'group-invariant, survives full lex-leader')


def t6():
    """Optional: byte-for-byte frame cross-check against the Lean-proven
    reference (lean/Conway99/Group.lean via `lake exe export_frame`)."""
    r = subprocess.run(
        [sys.executable, str(Path(__file__).parent / 'crosscheck_lean.py')],
        capture_output=True, text=True)
    if r.returncode == 2:
        print('T6 SKIP  %s' % r.stdout.strip())
        return
    assert r.returncode == 0, r.stdout + r.stderr
    print('T6 PASS  %s' % r.stdout.strip())


def main():
    t1()
    t2()
    t3()
    w = t4()
    t5()
    t6()
    print()
    print('All symmetry tests passed. Lex-leader machinery is trusted '
          '(Paley(9) reduction: 5040 -> %d with 28 elements).' % w)


if __name__ == '__main__':
    main()
