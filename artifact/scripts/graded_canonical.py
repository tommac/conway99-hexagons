#!/usr/bin/env python3
"""
graded_canonical.py -- THREAD B: the GRADED canonical split.

Log 031 certified ONE transition system dead (the canonical one, M_a(b)=b'
for all a,b).  This module builds the graded generalisation: instead of
asserting the canonical system, assert that a model AGREES with it in at
least m places, for a ladder of m.  Because the canonical system is the
unique G-invariant transition system (G = S2 wr S7, the residual skeleton
group), "agreement count >= m" is a G-INVARIANT constraint, so it composes
with the lex-leader layer of cnf/conway99_skel_sbA.cnf exactly as the 924
canonical units did.

THE TWO STATISTICS  (see section "verify" for the machine checks)

  c(X) = # of the 924 canonical LITERALS satisfied by X
         (the 924 index-sharing slots z_{ab} ~ z_{ac}, signed canonically)
  D(X) = # of the 84 canonical POSITIVE literals satisfied by X
         (the slots z_{ab} ~ z_{ab'} -- "a's transition on b is canonical")

On any model of the skeleton CNF these are affinely equivalent:

        c(X) = 756 + 2*D(X),        D(X) in {0,...,84}

because lambda=1 forces the 12 outside neighbours of each a in N(0) to
induce a PERFECT MATCHING, i.e. exactly 6 of that a's 66 slots are TRUE.
Writing d_a = |M_a & canonical_a| we get, per a,
   agreements = d_a  (true-true)  +  66 - (12 - d_a)  (false-false)
              = 54 + 2 d_a,   summed over 14 roots  =>  756 + 2D.

CONSEQUENCE THAT MATTERS FOR PLANNING: c is never below 756.  Any ladder
rung m <= 756 is VACUOUS -- "c >= m" is implied by the base instance, so
UNSAT there would be a solution of Conway-99 itself, not a graded result.
The honest ladder is on D, from D=84 (log 031's theorem) downwards.

Usage
  python3 scripts/graded_canonical.py verify [--full-group]
  python3 scripts/graded_canonical.py count
  python3 scripts/graded_canonical.py cardtest
  python3 scripts/graded_canonical.py scout --dmin 82 --confs 100000
  python3 scripts/graded_canonical.py gen --dmin 82 -o cnf/g82
  python3 scripts/graded_canonical.py gen --dmax 4  -o cnf/gu4
"""
import argparse
import json
import os
import random
import sys
import time
from collections import Counter
from itertools import combinations

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

MATCHED = [(1, 2), (3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (13, 14)]
PART = {}
for _a, _b in MATCHED:
    PART[_a], PART[_b] = _b, _a
NN = list(range(1, 15))
SKEL = 'cnf/conway99_skel_sbA'


# --------------------------------------------------------------------------
# the canonical literal set, in BOTH coordinate systems
#   * label coordinates  (pairs of frozensets)  -- used for the group action
#   * CNF variable ids   (from the instance map) -- used for the encoding
# --------------------------------------------------------------------------

def canonical_slots():
    """Return (pos, neg): lists of (labelA, labelB) label-pairs for the 84
    canonical-TRUE slots and the 840 canonical-FALSE slots."""
    pos, neg = [], []
    for a in NN:
        B = [u for u in NN if u not in (a, PART[a])]
        for b, c in combinations(B, 2):
            item = (frozenset((a, b)), frozenset((a, c)))
            (pos if PART[b] == c else neg).append(item)
    assert len(pos) == 84 and len(neg) == 840
    return pos, neg


def canonical_sextets():
    """The 84 canonical-TRUE slots grouped by root: {a: [6 label-pairs]}.
    G permutes the 14 roots (transitively) and carries sextet a to sextet
    g(a) -- so any statistic symmetric in the roots is G-invariant."""
    out = {}
    for a in NN:
        out[a] = [(frozenset((a, b)), frozenset((a, PART[b])))
                  for b in NN if b not in (a, PART[a])
                  and b < PART[b]]
        assert len(out[a]) == 6, (a, out[a])
    return out


def load_map(stem):
    m = json.load(open(stem + '.map.json'))
    vert = {frozenset(v): int(k) for k, v in m['pair_of'].items()}
    evar = {}
    for kk, val in m['evar'].items():
        i, j = (int(t) for t in kk.split(','))
        evar[(min(i, j), max(i, j))] = val
    assert len(vert) == 84 and len(evar) == 3486
    return vert, evar


def slot_var(vert, evar, L1, L2):
    p, q = vert[L1], vert[L2]
    return evar[(min(p, q), max(p, q))]


def maxd_clauses(t, top_id, stem=SKEL):
    """Clauses for the G-invariant condition

        MAXD >= t   :=   there is a root a in N(0) with d_a >= t

    (d_a = # of a's 6 matched pairs {b,b'} with M_a(b) = b').  One selector
    s_a per root, s_a -> AtLeast_t(a's 6 canonical slots) written directly as
    the C(6, 7-t) subset clauses, plus the disjunction s_1 v ... v s_14.

    Complete in both directions ON THE EDGE VARIABLES: if some d_a >= t the
    assignment extends (set s_a true exactly where d_a >= t), and any model
    has some s_a true hence some d_a >= t.  The projected model set is
    {X : max_a d_a >= t}, manifestly invariant under G (which permutes the
    roots and carries sextet a to sextet g(a))."""
    vert, evar = load_map(stem)
    sext = canonical_sextets()
    cls = []
    sel = []
    nxt = top_id
    for a in NN:
        nxt += 1
        s = nxt
        sel.append(s)
        lits = [slot_var(vert, evar, *p) for p in sext[a]]
        assert len(set(lits)) == 6
        for S in combinations(lits, 6 - t + 1):
            cls.append([-s] + list(S))
    cls.append(sel[:])
    return cls, nxt


def nbad_clauses(k, top_id, stem=SKEL):
    """Clauses for the G-invariant condition

        NBAD <= k   :=   at most k of the 14 roots a in N(0) are
                         non-canonical (d_a < 6)

    Defines e_a <-> (all 6 of a's canonical slots true) in both directions
    (so e_a is functionally determined and any satisfying edge assignment
    extends), then AtLeast_{14-k} over the e_a.  G permutes the roots, so
    the projected model set {X : #{a : d_a < 6} <= k} is G-invariant.

    NBAD <= 0 is exactly the canonical system (log 031)."""
    vert, evar = load_map(stem)
    sext = canonical_sextets()
    cls = []
    es = []
    nxt = top_id
    for a in NN:
        nxt += 1
        e = nxt
        es.append(e)
        lits = [slot_var(vert, evar, *p) for p in sext[a]]
        for l in lits:
            cls.append([-e, l])                      # e_a -> slot
        cls.append([e] + [-l for l in lits])         # all slots -> e_a
    extra, nxt = card_clauses(es, 14 - k, nxt, 'atleast')
    return cls + extra, nxt


def canonical_literals(stem=SKEL):
    """(pos_vars, neg_vars, all_lits): 84 positives, 840 negatives, and the
    924-literal canonical assumption set of log 031."""
    vert, evar = load_map(stem)
    pos, neg = canonical_slots()
    pv = [slot_var(vert, evar, *t) for t in pos]
    nv = [slot_var(vert, evar, *t) for t in neg]
    assert len(set(pv)) == 84 and len(set(nv)) == 840
    assert not (set(pv) & set(nv))
    return pv, nv, [v for v in pv] + [-v for v in nv]


def load_bvls243():
    """BvLS(243) = srg(243,22,1,2), reusing the adjudicator's verified
    constructor (scripts/adjudicate.py) without running its 83 checks:
    exec only the source prefix up to the line that builds it."""
    src_path = os.path.join(os.path.dirname(__file__), 'adjudicate.py')
    if not os.path.exists(src_path):
        return None
    src = open(src_path).read()
    marker = 'B243, CAP = bvls243()'
    if marker not in src:
        return None
    prefix = src.split(marker)[0]
    import io
    import contextlib
    ns = {'__name__': 'adj_prefix', '__file__': src_path}
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        exec(compile(prefix, src_path, 'exec'), ns)
        adj, _cap = ns['bvls243']()
    if isinstance(adj, dict):
        return {k: set(v) for k, v in adj.items()}
    return {i: set(s) for i, s in enumerate(adj)}


# --------------------------------------------------------------------------
# VERIFY: the soundness argument, mechanically
# --------------------------------------------------------------------------

def cmd_verify(args):
    import symmetry as sym
    ok = True

    def check(name, cond, detail=''):
        nonlocal ok
        ok = ok and bool(cond)
        print(f"  [{'PASS' if cond else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")

    print("V1. canonical literal set matches log 031's assumption set")
    pv, nv, lits = canonical_literals()
    # rebuild log 031's list independently, in its own order
    vert, evar = load_map(SKEL)
    ref = []
    for a in NN:
        B = [u for u in NN if u not in (a, PART[a])]
        for b, c in combinations(B, 2):
            v = slot_var(vert, evar, frozenset((a, b)), frozenset((a, c)))
            ref.append(v if PART[b] == c else -v)
    check("924 literals, identical as a set to canonical_sb.py's",
          len(ref) == 924 and set(ref) == set(lits))

    print("V2. the 84 canonical-TRUE slots are exactly one per (a, matched pair)")
    check("84 = 14 roots x 6 matched pairs of B_a", len(pv) == 84)

    print("V3. G-STABILITY of the canonical literal set (the whole argument)")
    lab_idx = sym.label_index()
    eidx = sym.edge_index()
    pos_lab, neg_lab = canonical_slots()

    def slot_id(L1, L2):
        u, v = lab_idx[tuple(sorted(L1))], lab_idx[tuple(sorted(L2))]
        return eidx[(min(u, v), max(u, v))]

    POS = frozenset(slot_id(*t) for t in pos_lab)
    NEG = frozenset(slot_id(*t) for t in neg_lab)
    check("84 distinct positive slot ids", len(POS) == 84)
    check("840 distinct negative slot ids, disjoint from POS",
          len(NEG) == 840 and not (POS & NEG))

    def image_pos(m_n):
        """image of POS under the wreath element with N(0)-permutation m_n,
        computed at LABEL level (independent of edge_perm)."""
        out = set()
        for L1, L2 in pos_lab:
            g1 = frozenset(m_n[t] for t in L1)
            g2 = frozenset(m_n[t] for t in L2)
            out.add(slot_id(g1, g2))
        return out

    # (a) exhaustive over the FULL group if asked, else structured + random
    from itertools import permutations, product
    if args.full_group:
        els = ((pi, s) for pi in permutations(range(7))
               for s in product((0, 1), repeat=7))
        total = 645120
        tag = "all 645,120 elements"
    else:
        els = sym.structured_elements() + sym.random_elements(3000, 20260809)
        total = len(els)
        tag = f"{total} elements (91 structured + 3000 random)"
    t0 = time.time()
    bad = 0
    n = 0
    for pi, s in els:
        m_n = sym.sigma_on_N(pi, s)
        if image_pos(m_n) != POS:
            bad += 1
        n += 1
    check(f"g(POS) = POS for {tag}", bad == 0 and n == total,
          f"({n} checked, {time.time()-t0:.0f}s)")

    # (b) the load-bearing code path (element_edge_perm) agrees with (a)
    bad = 0
    for pi, s in sym.structured_elements() + sym.random_elements(400, 7):
        P = sym.element_edge_perm(pi, s)   # slot t is compared against slot P[t]
        # X o P is the relabelled assignment; the image of slot set S is
        # {t : P[t] in S}
        img = {t for t in range(3486) if P[t] in POS}
        if img != POS:
            bad += 1
    check("edge_perm image of POS = POS (491 elements, real code path)", bad == 0)

    # (c) NEG is stable too (follows, but check it)
    bad = 0
    for pi, s in sym.structured_elements() + sym.random_elements(400, 8):
        P = sym.element_edge_perm(pi, s)
        if {t for t in range(3486) if P[t] in NEG} != NEG:
            bad += 1
    check("edge_perm image of NEG = NEG", bad == 0)

    print("V4. c and D are G-invariant statistics on assignments")
    rng = random.Random(31337)
    bad = 0
    for _ in range(300):
        X = [rng.randrange(2) for _ in range(3486)]
        pi, s = sym.random_elements(1, rng.randrange(10 ** 9))[0]
        P = sym.element_edge_perm(pi, s)
        Y = [X[P[t]] for t in range(3486)]          # the relabelled assignment
        cX = sum(X[t] for t in POS) + sum(1 - X[t] for t in NEG)
        cY = sum(Y[t] for t in POS) + sum(1 - Y[t] for t in NEG)
        dX = sum(X[t] for t in POS)
        dY = sum(Y[t] for t in POS)
        if (cX, dX) != (cY, dY):
            bad += 1
    check("c(g.X) = c(X) and D(g.X) = D(X) on 300 random assignments", bad == 0)

    print("V5. c = 756 + 2D on genuine transition systems (all 10395^14 have"
          " 6 true per root; sample)")
    bad = 0
    worst = (10 ** 9, -1)
    hist = Counter()
    for _ in range(4000):
        X = [0] * 3486
        D = 0
        for a in NN:
            B = [u for u in NN if u not in (a, PART[a])]
            rng.shuffle(B)
            for i in range(0, 12, 2):
                b, c = B[i], B[i + 1]
                X[slot_id(frozenset((a, b)), frozenset((a, c)))] = 1
                if PART[b] == c:
                    D += 1
        c = sum(X[t] for t in POS) + sum(1 - X[t] for t in NEG)
        if c != 756 + 2 * D:
            bad += 1
        hist[D] += 1
        worst = (min(worst[0], D), max(worst[1], D))
    check("c = 756 + 2D on 4000 random transition systems", bad == 0,
          f"D observed in [{worst[0]},{worst[1]}], mean {sum(k*v for k,v in hist.items())/4000:.2f}")

    print("V6. ground truth: both known lambda=1,mu=2 graphs sit at D = D_max")

    def D_of(adj, x):
        """D at root x: # (a, matched pair {b,b'}) with M_a(b) = b'.
        T[a] is stored as a symmetric dict, so halve."""
        import transition as tr
        ts = tr.transition_system(adj, x)
        N, part, T = ts['N'], ts['partner'], ts['T']
        d = sum(1 for a in N for b, c in T[a].items() if part[b] == c) // 2
        dmax = len(N) * ((len(N) - 2) // 2)
        return d, dmax

    import transition as tr
    g9 = tr.paley9()
    res = [D_of(g9, x) for x in g9]
    check("Paley(9) srg(9,4,1,2): D = D_max at all 9 roots",
          all(d == dm for d, dm in res),
          f"D={sorted({d for d,_ in res})}, D_max={res[0][1]}")

    adj243 = load_bvls243()
    if adj243 is None:
        check("BvLS(243) available", False, "could not build it")
    else:
        assert tr.srg_params(adj243) == (243, 22, 1, 2)
        roots = sorted(adj243)[:args.n243]
        res = [D_of(adj243, x) for x in roots]
        check(f"BvLS(243) srg(243,22,1,2): D = D_max at {len(roots)} roots"
              " (19!! = 654,729,075 systems a priori per root)",
              all(d == dm for d, dm in res),
              f"D={sorted({d for d,_ in res})}, D_max={res[0][1]}")

    print("V7. the LOCAL family MAXD >= t: G-invariance and encoding semantics")
    sext = canonical_sextets()
    SEXT = {a: frozenset(slot_id(*p) for p in sext[a]) for a in NN}
    assert len(set().union(*SEXT.values())) == 84
    bad = 0
    for pi, s in sym.structured_elements() + sym.random_elements(600, 11):
        P = sym.element_edge_perm(pi, s)
        img = {frozenset(t for t in range(3486) if P[t] in SEXT[a]) for a in NN}
        if img != set(SEXT.values()):
            bad += 1
    check("G permutes the 14 canonical sextets as blocks (691 elements)", bad == 0)
    m_n_targets = set()
    for pi, s in sym.random_elements(2000, 12):
        m_n = sym.sigma_on_N(pi, s)
        m_n_targets.add(m_n[1])
    check("G acts transitively on the 14 roots", len(m_n_targets) == 14,
          f"images of root 1: {sorted(m_n_targets)}")

    from pysat.solvers import Glucose42 as _G
    vert, evar = load_map(SKEL)
    slotvar = {}
    for a in NN:
        for p in sext[a]:
            slotvar[slot_id(*p)] = slot_var(vert, evar, *p)
    allpos = sorted(slotvar)
    bad = 0
    for t in (1, 2, 3, 4, 6):
        cls, top = maxd_clauses(t, 10 ** 6)
        sv = _G(bootstrap_with=cls)
        for _ in range(200):
            X = [0] * 3486
            for a in NN:
                B = [u for u in NN if u not in (a, PART[a])]
                rng.shuffle(B)
                for i in range(0, 12, 2):
                    X[slot_id(frozenset((a, B[i])), frozenset((a, B[i + 1])))] = 1
            want = max(sum(X[q] for q in SEXT[a]) for a in NN) >= t
            asm = [slotvar[q] if X[q] else -slotvar[q] for q in allpos]
            if sv.solve(assumptions=asm) != want:
                bad += 1
        sv.delete()
    check("MAXD>=t encoding == max_a d_a >= t (t=1,2,3,4,6; 1000 systems)",
          bad == 0)

    print()
    print("VERDICT:", "ALL CHECKS PASS" if ok else "*** FAILURES ***")
    return 0 if ok else 1


# --------------------------------------------------------------------------
# COUNT: how much of the transition-system space does "D >= m" carve out?
# --------------------------------------------------------------------------

def matchings_meeting(nhalf, d):
    """# perfect matchings on 2*nhalf labelled points meeting a fixed perfect
    matching in exactly d edges."""
    from math import comb
    # choose the d kept edges, then match the remaining 2(nhalf-d) points
    # with none of their canonical partners
    def avoid(j):
        """# perfect matchings on 2j points, none of which is a canonical edge"""
        # inclusion-exclusion over how many canonical edges are used
        from math import comb as C
        tot = 0
        for i in range(j + 1):
            tot += (-1) ** i * C(j, i) * dfact(2 * (j - i) - 1)
        return tot
    return comb(nhalf, d) * avoid(nhalf - d)


def dfact(n):
    """double factorial n!! for odd n >= -1"""
    r = 1
    while n > 1:
        r *= n
        n -= 2
    return r


def cmd_count(args):
    from math import comb
    per = [matchings_meeting(6, d) for d in range(7)]
    tot1 = sum(per)
    print(f"perfect matchings on 12 points: {tot1} (expect 11!! = {dfact(11)})")
    assert tot1 == dfact(11) == 10395
    print("  d = |M_a & canonical_a| :")
    for d, v in enumerate(per):
        print(f"    d={d}: {v:6d}   ({100*v/tot1:6.3f}%)")
    print("  note d=5 is impossible (a matching agreeing in 5 of 6 agrees in 6)")

    # distribution of D = sum of 14 iid copies
    poly = [1]
    for _ in range(14):
        new = [0] * (len(poly) + 6)
        for i, ci in enumerate(poly):
            if ci:
                for d, v in enumerate(per):
                    new[i + d] += ci * v
        poly = new
    total = sum(poly)
    assert total == 10395 ** 14
    print(f"\ntotal transition systems: 10395^14 = {total}")
    tail = [0] * (86)
    acc = 0
    for D in range(84, -1, -1):
        acc += poly[D]
        tail[D] = acc
    print("\n  D>=m ladder (labelled counts; |G| = 645,120):")
    print("   m    #systems with D>=m        fraction of 10395^14      /|G|")
    for m in [84, 83, 82, 80, 78, 76, 72, 70, 64, 56, 48, 42, 28, 14, 7, 1, 0]:
        f = tail[m] / total
        print(f"  {m:3d}  {tail[m]:>26d}  {f:>22.6e}  {tail[m]/645120:>18.4g}")
    print("\n  low end (the DUAL split, D<=m):")
    head = 0
    for m in range(0, 9):
        head += poly[m]
        print(f"   D<={m}: {head:>26d}   fraction {head/total:.6f}")
    # ---- the LOCAL family: coverage of "some root a has d_a >= t" ---------
    print("\n  LOCAL family MAXD >= t  (some root a in N(0) has d_a >= t):")
    print("   t   per-root P[d>=t]      P[MAXD>=t]        #systems")
    for t in range(6, 0, -1):
        pt = sum(per[d] for d in range(t, 7))
        q = (tot1 - pt) ** 14
        cnt = total - q
        print(f"  {t}   {pt/tot1:.6f}            {cnt/total:.6f}      {cnt}")
    # mean / sd
    mean = sum(D * poly[D] for D in range(85)) / total
    var = sum((D - mean) ** 2 * poly[D] for D in range(85)) / total
    print(f"\n  E[D] = {mean:.4f}, sd = {var**0.5:.4f}  "
          f"(per root E[d] = {mean/14:.4f})")
    return 0


# --------------------------------------------------------------------------
# CARDINALITY ENCODING + its semantic test
# --------------------------------------------------------------------------

def card_clauses(lits, bound, top_id, mode):
    """mode 'atleast' -> at least `bound` of `lits` true;
       mode 'atmost'  -> at most  `bound` of `lits` true.
    Returns (clauses, new_top_id)."""
    from pysat.card import CardEnc, EncType
    if mode == 'atleast':
        cnf = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id,
                              encoding=EncType.seqcounter)
    else:
        cnf = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id,
                             encoding=EncType.seqcounter)
    cls = [list(c) for c in cnf.clauses]
    nt = top_id
    for c in cls:
        for l in c:
            nt = max(nt, abs(l))
    return cls, nt


def cmd_cardtest(args):
    """Assert the semantics of the cardinality encoding by brute force:
    for n inputs and every bound, enumerate all 2^n input assignments and
    check that an aux extension exists iff the count condition holds."""
    from pysat.solvers import Glucose42
    ok = True
    for n in range(1, 9):
        lits = list(range(1, n + 1))
        for mode in ('atleast', 'atmost'):
            for bound in range(0, n + 1):
                cls, top = card_clauses(lits, bound, n, mode)
                s = Glucose42(bootstrap_with=cls)
                for mask in range(1 << n):
                    asm = [(i + 1) if (mask >> i) & 1 else -(i + 1)
                           for i in range(n)]
                    cnt = bin(mask).count('1')
                    want = (cnt >= bound) if mode == 'atleast' else (cnt <= bound)
                    got = s.solve(assumptions=asm)
                    if got != want:
                        ok = False
                        print(f"  FAIL n={n} {mode} bound={bound} mask={mask}: "
                              f"want {want} got {got}")
                s.delete()
        print(f"  n={n}: all bounds x all 2^{n} assignments OK")
    # and the real shape: 84 literals, mixed signs, spot-checked
    print("  spot check at n=84 (the real width), random assignments:")
    rng = random.Random(5)
    lits = [(i + 1) if i % 3 else -(i + 1) for i in range(84)]
    for bound in (0, 1, 40, 82, 83, 84):
        cls, top = card_clauses(lits, bound, 84, 'atleast')
        s = Glucose42(bootstrap_with=cls)
        for _ in range(200):
            val = [rng.randrange(2) for _ in range(84)]
            asm = [(i + 1) if val[i] else -(i + 1) for i in range(84)]
            cnt = sum(1 for i, l in enumerate(lits)
                      if (val[i] == 1) == (l > 0))
            if s.solve(assumptions=asm) != (cnt >= bound):
                ok = False
                print(f"  FAIL wide atleast bound={bound}")
        s.delete()
        print(f"    bound={bound}: OK")
    print("VERDICT:", "CARD ENCODING SEMANTICS VERIFIED" if ok else "*** FAIL ***")
    return 0 if ok else 1


# --------------------------------------------------------------------------
# instance construction
# --------------------------------------------------------------------------

def build(dmin=None, dmax=None, cmin=None, maxd=None, stem=None, nbad=None):
    stem = stem or SKEL
    """Return (header_nv, extra_clauses, description).  Reads only the map."""
    pv, nv, lits924 = canonical_literals(stem)
    m = json.load(open(stem + '.map.json'))
    # top var id: read the CNF header lazily instead (map has no nv)
    with open(stem + '.cnf') as fh:
        for line in fh:
            if line.startswith('p cnf'):
                _, _, nvars, nclauses = line.split()
                break
    nvars, nclauses = int(nvars), int(nclauses)
    if nbad is not None:
        cls, top = nbad_clauses(nbad, nvars, stem)
        desc = f"NBAD <= {nbad}: at most {nbad} of the 14 roots non-canonical"
    elif maxd is not None:
        cls, top = maxd_clauses(maxd, nvars, stem)
        desc = f"MAXD >= {maxd}: some root a in N(0) has d_a >= {maxd}"
    elif cmin is not None:
        cls, top = card_clauses(lits924, cmin, nvars, 'atleast')
        desc = f"c >= {cmin} of 924 canonical literals"
    elif dmin is not None:
        cls, top = card_clauses(pv, dmin, nvars, 'atleast')
        desc = f"D >= {dmin} of 84 canonical transitions"
    elif dmax is not None:
        cls, top = card_clauses(pv, dmax, nvars, 'atmost')
        desc = f"D <= {dmax} of 84 canonical transitions"
    else:
        raise SystemExit("need --dmin / --dmax / --cmin")
    return nvars, nclauses, cls, top, desc


def cmd_gen(args):
    stem = getattr(args, 'base', None) or SKEL
    nvars, nclauses, cls, top, desc = build(args.dmin, args.dmax, args.cmin,
                                            getattr(args, 'maxd', None), stem,
                                            getattr(args, 'nbad', None))
    out = args.out + '.cnf'
    t0 = time.time()
    with open(out, 'w') as w, open(stem + '.cnf') as r:
        w.write(f"p cnf {top} {nclauses + len(cls)}\n")
        for line in r:
            if line.startswith('p cnf') or line.startswith('c'):
                continue
            w.write(line)
        for c in cls:
            w.write(' '.join(map(str, c)) + ' 0\n')
    print(f"{out}: {top} vars, {nclauses + len(cls)} clauses "
          f"(+{len(cls)} for '{desc}'), {time.time()-t0:.0f}s, "
          f"{os.path.getsize(out)/2**20:.0f} MiB")
    json.dump({'base': stem, 'constraint': desc, 'card_clauses': len(cls),
               'nv': top, 'nclauses': nclauses + len(cls)},
              open(args.out + '.graded.json', 'w'), indent=1)
    return 0


def cmd_scout(args):
    from pysat.formula import CNF
    from pysat.solvers import Glucose42
    nvars, nclauses, cls, top, desc = build(args.dmin, args.dmax, args.cmin,
                                            getattr(args, 'maxd', None),
                                            getattr(args, 'base', None),
                                            getattr(args, 'nbad', None))
    t0 = time.time()
    f = CNF(from_file=SKEL + '.cnf')
    print(f"base {SKEL}: {f.nv} vars {len(f.clauses)} clauses "
          f"({time.time()-t0:.0f}s)", flush=True)
    s = Glucose42(bootstrap_with=f.clauses)
    for c in cls:
        s.add_clause(c)
    print(f"+ {len(cls)} clauses for '{desc}'", flush=True)
    ok, lits = s.propagate()
    print(f"UP conflict: {not ok}", flush=True)
    if ok:
        s.conf_budget(args.confs)
        t1 = time.time()
        r = s.solve_limited()
        verdict = {True: 'SAT', False: 'UNSAT', None: 'UNKNOWN'}[r]
        print(f"VERDICT {verdict}   budget {args.confs}  {time.time()-t1:.0f}s",
              flush=True)
        st = s.accum_stats()
        print("stats:", st, flush=True)
    else:
        print("VERDICT UNSAT (by unit propagation)", flush=True)
    s.delete()
    return 0


def cmd_ladder(args):
    """Scout a whole ladder of rungs, parsing the 106 MiB base CNF ONCE."""
    from pysat.formula import CNF
    from pysat.solvers import Glucose42
    stem = args.base or SKEL
    t0 = time.time()
    f = CNF(from_file=stem + '.cnf')
    base = f.clauses
    nvars = f.nv
    print(f"base {stem}: {nvars} vars {len(base)} clauses "
          f"(parsed in {time.time()-t0:.0f}s)", flush=True)
    pv, nv_, lits924 = canonical_literals(stem)
    rungs = []
    for m in (args.dmin or []):
        rungs.append(('D>=%d' % m, pv, m, 'atleast'))
    for m in (args.dmax or []):
        rungs.append(('D<=%d' % m, pv, m, 'atmost'))
    for m in (args.cmin or []):
        rungs.append(('c>=%d' % m, lits924, m, 'atleast'))
    for t in (args.maxd or []):
        rungs.append(('MAXD>=%d' % t, None, t, 'maxd'))
    for k in (args.nbad or []):
        rungs.append(('NBAD<=%d' % k, None, k, 'nbad'))
    out = []
    for name, lits, bound, mode in rungs:
        if mode == 'maxd':
            cls, top = maxd_clauses(bound, nvars, stem)
        elif mode == 'nbad':
            cls, top = nbad_clauses(bound, nvars, stem)
        else:
            cls, top = card_clauses(lits, bound, nvars, mode)
        s = Glucose42(bootstrap_with=base)
        for c in cls:
            s.add_clause(c)
        ok, _ = s.propagate()
        if not ok:
            rec = dict(rung=name, base=stem, verdict='UNSAT', by='unit-propagation',
                       conflicts=0, secs=0.0, card_clauses=len(cls))
        else:
            s.conf_budget(args.confs)
            t1 = time.time()
            r = s.solve_limited()
            st = s.accum_stats()
            rec = dict(rung=name, base=stem,
                       verdict={True: 'SAT', False: 'UNSAT', None: 'UNKNOWN'}[r],
                       by='search', conflicts=st.get('conflicts'),
                       decisions=st.get('decisions'), props=st.get('propagations'),
                       secs=round(time.time() - t1, 1), card_clauses=len(cls),
                       budget=args.confs)
        s.delete()
        print(json.dumps(rec), flush=True)
        out.append(rec)
        if args.ledger:
            with open(args.ledger, 'a') as w:
                w.write(json.dumps(rec) + '\n')
    return 0


def cmd_orbits(args):
    """EXACT number of G-orbits of transition systems in each ladder rung.

    A transition system is the 84-element set {(a, {b,c}) : M_a(b) = c},
    i.e. a subset of the 924 index-sharing slots-with-root.  G acts on the
    924 by (a,{b,c}) -> (g a, {g b, g c}).  Orbits are counted by BFS under
    three generators of G = S2 wr S7 (sign flip on pair 0; transposition of
    pairs 0,1; the 7-cycle on pairs) -- these generate the whole group,
    asserted below by closing the orbit of a random point and comparing
    with the 645,120 explicit elements' images."""
    import symmetry as sym
    from itertools import permutations, product

    # global slot index (a, frozenset{b,c}) -> 0..923
    sid, slots = {}, []
    for a in NN:
        B = [u for u in NN if u not in (a, PART[a])]
        for b, c in combinations(B, 2):
            sid[(a, frozenset((b, c)))] = len(slots)
            slots.append((a, frozenset((b, c))))
    assert len(slots) == 924

    def perm_of(m_n):
        return tuple(sid[(m_n[a], frozenset(m_n[t] for t in bc))]
                     for a, bc in slots)

    idp = tuple(range(7))
    gens = []
    s = [0] * 7
    s[0] = 1
    gens.append(sym.sigma_on_N(idp, tuple(s)))                 # sign flip
    pi = list(idp)
    pi[0], pi[1] = pi[1], pi[0]
    gens.append(sym.sigma_on_N(tuple(pi), (0,) * 7))           # transposition
    gens.append(sym.sigma_on_N(tuple((i + 1) % 7 for i in range(7)), (0,) * 7))
    GP = [perm_of(m) for m in gens]

    # assert the three generate G, cheaply: close them as permutations of
    # N(0) (14 points) and compare the order with |S2 wr S7| = 645,120
    key = lambda m: tuple(m[t] for t in NN)
    idm = {t: t for t in NN}
    seen = {key(idm)}
    frontier = [idm]
    while frontier:
        nf = []
        for m in frontier:
            for q in gens:
                r = {t: q[m[t]] for t in NN}
                k = key(r)
                if k not in seen:
                    seen.add(k)
                    nf.append(r)
        frontier = nf
    print(f"group generated by the 3 elements has order {len(seen)} "
          f"(expected 645120): {len(seen) == 645120}")
    assert len(seen) == 645120, "the three elements do not generate G"

    # per-root matchings by deficit
    per_root = {}
    for a in NN:
        B = [u for u in NN if u not in (a, PART[a])]
        canon = {frozenset((b, PART[b])) for b in B}
        byd = {}
        def rec(rem, acc):
            if not rem:
                d = len(set(acc) & canon)
                byd.setdefault(6 - d, []).append(tuple(sorted(
                    sid[(a, e)] for e in acc)))
                return
            x = rem[0]
            for i in range(1, len(rem)):
                rec(rem[1:i] + rem[i + 1:], acc + [frozenset((x, rem[i]))])
        rec(tuple(B), [])
        per_root[a] = byd
    assert sum(len(v) for v in per_root[1].values()) == 10395

    print("\n rung   #systems   #G-orbits   representative deficit patterns")
    for m in args.m:
        budget = 84 - m
        # deficit vectors over 14 roots with sum <= budget, entries in {0,2,3,4,5,6}
        sysset = []
        def build(i, left, acc):
            if i == 14:
                # cartesian product of the chosen per-root matchings
                stack = [()]
                for a, dd in zip(NN, acc):
                    stack = [t + mm for t in stack for mm in per_root[a][dd]]
                sysset.extend(tuple(sorted(t)) for t in stack)
                return
            for dd in (0, 2, 3, 4, 5, 6):
                if dd <= left and per_root[NN[i]].get(dd):
                    build(i + 1, left - dd, acc + [dd])
        build(0, budget, [])
        if len(sysset) > args.cap:
            print(f"  D>={m:3d}  {len(sysset):9d}   (skipped: above --cap "
                  f"{args.cap}; lower bound #/|G| = "
                  f"{len(sysset)/645120:.1f} orbits)")
            continue
        S = set(sysset)
        norb = 0
        sizes = []
        pending = set(S)
        while pending:
            x = pending.pop()
            comp = {x}
            fr = [x]
            while fr:
                nf = []
                for y in fr:
                    for q in GP:
                        z = tuple(sorted(q[i] for i in y))
                        if z not in comp:
                            comp.add(z)
                            nf.append(z)
                fr = nf
            assert comp <= S, "rung not G-invariant -- SOUNDNESS BUG"
            pending -= comp
            norb += 1
            sizes.append(len(comp))
        print(f"  D>={m:3d}  {len(S):9d}   {norb:9d}   orbit sizes "
              f"{sorted(sizes)}")
    return 0


def cmd_sbcanon(args):
    """Build an ORDER-ALIGNED symmetry-broken base (log 007's principle).

    sbA compares the 3,486 edge slots in the canonical row-major order; the
    84 canonical-transition slots are scattered through it, so the lex chains
    stall on unknowns long before they reach the variables the graded
    constraint touches.  This builds the same 91 structured lex-leader
    constraints under the order

        [the 84 canonical slots, ascending] ++ [everything else, ascending]

    ONE order for the whole instance (mixing orders inside an instance is
    UNSOUND); sound for any single order by lexLeader_mixed_equisat, which
    is order-agnostic (Lean, sorry-free).  Output: cnf/conway99_skel_sbCF.*
    """
    import symmetry as sym
    base = getattr(args, 'skel', None) or 'cnf/conway99_skel'
    meta = json.load(open(base + '.map.json'))
    assert meta['skeleton']
    labels = sym.outside_labels()
    pair_of = {int(k): tuple(v) for k, v in meta['pair_of'].items()}
    for i, lab in enumerate(labels):
        assert pair_of[15 + i] == lab, 'frame mismatch encoder vs symmetry.py'
    evar = {}
    for key, var in meta['evar'].items():
        i, j = map(int, key.split(','))
        evar[(i, j)] = var
    pos = sym.edge_positions()
    eidx = sym.edge_index()
    lab_idx = sym.label_index()
    xvars = [evar[(15 + u, 15 + v)] for u, v in pos]

    pos_lab, _ = canonical_slots()
    POS = sorted(eidx[tuple(sorted((lab_idx[tuple(sorted(L1))],
                                    lab_idx[tuple(sorted(L2))])))]
                 for L1, L2 in pos_lab)
    assert len(set(POS)) == 84
    order = POS + [t for t in range(len(pos)) if t not in set(POS)]
    assert sorted(order) == list(range(3486))

    with open(base + '.cnf') as f:
        header = f.readline().split()
    nv, ncl = int(header[2]), int(header[3])
    next_aux = nv + 1
    sb = []
    for pi, signs in sym.structured_elements():
        P = sym.element_edge_perm(pi, signs)
        cls, next_aux = sym.lex_leader_clauses(xvars, P, next_aux, None, order)
        sb.extend(cls)
    out = args.out
    with open(base + '.cnf') as fin, open(out + '.cnf', 'w') as fo:
        fin.readline()
        fo.write('p cnf %d %d\n' % (next_aux - 1, ncl + len(sb)))
        for line in fin:
            fo.write(line)
        for c in sb:
            fo.write(' '.join(map(str, c)) + ' 0\n')
    import shutil
    shutil.copy(base + '.map.json', out + '.map.json')
    json.dump({'base': base + '.cnf', 'structured': True, 'n_structured': 91,
               'sb_order': 'canon-first', 'order_head': POS[:12],
               'sb_clauses': len(sb), 'total_vars': next_aux - 1,
               'total_clauses': ncl + len(sb)},
              open(out + '.sb.json', 'w'), indent=1)
    print(f"{out}.cnf: {next_aux-1} vars, {ncl+len(sb)} clauses "
          f"(+{len(sb)} lex under canon-first order), "
          f"{os.path.getsize(out + '.cnf')/2**20:.0f} MiB")
    return 0


def sha256(path):
    import hashlib
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b''):
            h.update(chunk)
    return h.hexdigest()


def cmd_certify(args):
    """Full certified pipeline for ONE rung, log-020 style:
    generate -> sha -> glucose42 DRAT -> drat-trim -> (cake_lpr) -> DELETE.
    Only hashes survive."""
    import shutil
    import subprocess
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    assert os.path.exists(os.path.join(root, 'src', 'solve.py')), root
    free = shutil.disk_usage(root).free / 2 ** 30
    print(f"free disk: {free:.2f} GiB", flush=True)
    if free < args.min_free:
        print(f"ABORT: need >= {args.min_free} GiB free")
        return 1
    tag = (f"d{args.dmin}" if args.dmin is not None else
           f"u{args.dmax}" if args.dmax is not None else
           f"maxd{args.maxd}" if args.maxd is not None else
           f"nbad{args.nbad}" if args.nbad is not None else f"c{args.cmin}")
    stem = args.stem or os.path.join('cnf', f'graded_{tag}')
    ns = argparse.Namespace(dmin=args.dmin, dmax=args.dmax, cmin=args.cmin,
                            maxd=args.maxd, nbad=args.nbad,
                            base=args.base, out=stem)
    cmd_gen(ns)
    cnf, drat, lrat = stem + '.cnf', stem + '.drat', stem + '.lrat'
    meta_g = json.load(open(stem + '.graded.json'))
    rec = {'rung': tag, 'dmin': args.dmin, 'nv': meta_g['nv'],
           'nclauses': meta_g['nclauses'], 'card_clauses': meta_g['card_clauses'],
           'cnf': cnf, 'cnf_sha256': sha256(cnf),
           'cnf_bytes': os.path.getsize(cnf), 'solver': args.solver}
    print(f"cnf sha256 {rec['cnf_sha256']} (solver={args.solver})", flush=True)
    t0 = time.time()
    if args.solver == 'cadical':
        cadical_bin = shutil.which('cadical') or '/opt/homebrew/bin/cadical'
        cmd = [cadical_bin, '-q', '-n']
        if args.confs and args.confs > 0:
            cmd += ['-c', str(args.confs)]
        if args.ascii_drat:
            cmd += ['--binary=false']
        cmd += [cnf, drat]
        r = subprocess.run(cmd, capture_output=True, text=True)
    else:
        r = subprocess.run([sys.executable, os.path.join(root, 'src', 'solve.py'),
                            cnf, '--proof', drat, '--confs', str(args.confs)],
                           capture_output=True, text=True)
    sys.stdout.write(r.stdout)
    rec['solve_secs'] = round(time.time() - t0, 1)
    rec['solver_rc'] = r.returncode
    if r.returncode != 20:
        rec['verdict'] = {10: 'SAT', 0: 'UNKNOWN'}.get(r.returncode, 'ERROR')
        print("not UNSAT:", rec['verdict'], flush=True)
        sys.stderr.write(r.stderr[-2000:])
        for p in (cnf, drat):
            if os.path.exists(p) and not args.keep:
                os.remove(p)
        print(json.dumps(rec), flush=True)
        if args.ledger:
            open(args.ledger, 'a').write(json.dumps(rec) + '\n')
        return 0
    rec['drat_bytes'] = os.path.getsize(drat)
    rec['drat_sha256'] = sha256(drat)
    dt = (args.drat_trim or os.environ.get('DRAT_TRIM') or
          shutil.which('drat-trim') or
          os.path.join(root, 'tools', 'drat-trim', 'drat-trim'))
    argv = [dt, cnf, drat] + (['-L', lrat] if args.lrat else [])
    t0 = time.time()
    c = subprocess.run(argv, capture_output=True, text=True)
    rec['drat_trim_secs'] = round(time.time() - t0, 1)
    rec['drat_trim'] = 's VERIFIED' in c.stdout
    for line in c.stdout.splitlines():
        if line.startswith('s ') or 'resolution' in line or 'CORE' in line \
                or 'LEMMAS' in line:
            print('drat-trim:', line.strip(), flush=True)
    if args.lrat and rec['drat_trim'] and os.path.exists(lrat):
        rec['lrat_bytes'] = os.path.getsize(lrat)
        rec['lrat_sha256'] = sha256(lrat)
        ck = (args.cake_lpr or os.environ.get('CAKE_LPR') or
              shutil.which('cake_lpr') or
              os.path.join(root, 'tools', 'cake_lpr', 'cake_lpr'))
        t0 = time.time()
        k = subprocess.run([ck, cnf, lrat], capture_output=True, text=True)
        rec['cake_lpr_secs'] = round(time.time() - t0, 1)
        rec['cake_lpr'] = 'VERIFIED UNSAT' in k.stdout
        print('cake_lpr:', k.stdout.strip()[:200], flush=True)
    dual_ok = rec['drat_trim'] and (not args.lrat or rec.get('cake_lpr', False))
    rec['verdict'] = 'UNSAT' if dual_ok else 'PROOF-FAILED'
    if not args.keep:
        for p in (cnf, drat, lrat):
            if os.path.exists(p):
                os.remove(p)
    print(json.dumps(rec), flush=True)
    if args.ledger:
        open(args.ledger, 'a').write(json.dumps(rec) + '\n')
    return 0 if dual_ok else 1


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    v = sub.add_parser('verify')
    v.add_argument('--full-group', action='store_true')
    v.add_argument('--n243', type=int, default=6,
                   help='how many roots of BvLS(243) to test (243 = all)')
    sub.add_parser('count')
    sub.add_parser('cardtest')
    for name in ('gen', 'scout'):
        p = sub.add_parser(name)
        p.add_argument('--dmin', type=int)
        p.add_argument('--dmax', type=int)
        p.add_argument('--cmin', type=int)
        p.add_argument('--maxd', type=int)
        p.add_argument('--nbad', type=int)
        p.add_argument('--base')
        if name == 'gen':
            p.add_argument('-o', '--out', required=True)
        else:
            p.add_argument('--confs', type=int, default=100000)
    p = sub.add_parser('ladder')
    p.add_argument('--dmin', type=int, nargs='*')
    p.add_argument('--dmax', type=int, nargs='*')
    p.add_argument('--cmin', type=int, nargs='*')
    p.add_argument('--maxd', type=int, nargs='*')
    p.add_argument('--nbad', type=int, nargs='*')
    p.add_argument('--base')
    p.add_argument('--confs', type=int, default=100000)
    p.add_argument('--ledger')
    p = sub.add_parser('sbcanon')
    p.add_argument('--skel', default='cnf/conway99_skel')
    p.add_argument('-o', '--out', default='cnf/conway99_skel_sbCF')

    p = sub.add_parser('orbits')
    p.add_argument('--m', type=int, nargs='+', default=[84, 82, 81, 80])
    p.add_argument('--cap', type=int, default=200000,
                   help='skip orbit BFS above this many systems (memory)')

    p = sub.add_parser('certify')
    p.add_argument('--dmin', type=int)
    p.add_argument('--dmax', type=int)
    p.add_argument('--cmin', type=int)
    p.add_argument('--maxd', type=int)
    p.add_argument('--nbad', type=int)
    p.add_argument('--base')
    p.add_argument('--solver', choices=('cadical', 'glucose42'), default='cadical')
    p.add_argument('--ascii-drat', action='store_true')
    p.add_argument('--confs', type=int, default=0)
    p.add_argument('--stem')
    p.add_argument('--ledger')
    p.add_argument('--lrat', action='store_true')
    p.add_argument('--drat-trim')
    p.add_argument('--cake-lpr')
    p.add_argument('--keep', action='store_true')
    p.add_argument('--min-free', type=float, default=1.2)
    a = ap.parse_args()
    return {'verify': cmd_verify, 'count': cmd_count, 'cardtest': cmd_cardtest,
            'gen': cmd_gen, 'scout': cmd_scout, 'ladder': cmd_ladder,
            'certify': cmd_certify, 'orbits': cmd_orbits,
            'sbcanon': cmd_sbcanon}[a.cmd](a)


if __name__ == '__main__':
    sys.exit(main())
