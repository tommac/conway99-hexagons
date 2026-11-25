#!/usr/bin/env python3
"""
symmetry.py — residual symmetry group of the Conway-99 skeleton and
lex-leader symmetry-breaking constraints (roadmap item 1).

THE GROUP.  The canonical skeleton (encode.py --conway-skeleton) fixes
vertex 0, the matching M = {1,2},{3,4},...,{13,14} on N(0), and labels the
84 outside vertices by the non-matched pairs of N(0) in lexicographic
order.  A vertex permutation preserving the skeleton must fix 0 and
permute N(0) preserving M — and is then FORCED on the outside vertices,
because an outside vertex's label is determined by its adjacencies into
N(0): the vertex labeled {a,b} must go to the one labeled {s(a),s(b)}.
So the residual group is exactly the matching stabilizer

    G = S2 wr S7  (wreath product),   |G| = 7! * 2^7 = 645,120,

an element being (pi, signs): pi permutes the 7 matched pairs, signs says
which pairs land with their two members swapped.

WHY ADDING LEX CONSTRAINTS IS SOUND.  Fix once and for all the sequence of
the 3,486 outside-edge slots (edge_positions(): label-index pairs (u,v),
u<v, row-major upper triangle).  Each g in G induces a permutation P_g of
those slots (relabel both endpoints, re-sort).  test_symmetry.py verifies
computationally that relabeling the full 99-vertex graph by g (a) preserves
the skeleton exactly and (b) carries the outside-edge vector X to X o P
with P from this module — so an assignment X satisfies the SRG constraints
iff X o P_g does, and the solution set is a union of orbits {X o P_g}.
The lex-minimum X* of an orbit satisfies X* <=_lex X* o P_g for EVERY
g in G.  Hence adding

    X <=_lex X o P_g      for g in ANY subset S of G

preserves satisfiability exactly: at least one member of every solution
orbit survives, and every eliminated assignment is a relabeling of a
surviving one.  UNSAT of the constrained instance therefore still means
UNSAT of the original.  Prefix truncation is likewise sound:
X <=_lex Y implies prefix_L(X) <=_lex prefix_L(Y) for every L.

THE ENCODING.  x <=_lex y over positions t = 0..n-1 uses the standard
chain of "prefixes equal so far" auxiliaries a_t:

    a_{t-1} -> (x_t <= y_t)              [~a_{t-1} | ~x_t | y_t]
    a_{t-1} &  x_t &  y_t -> a_t         [~a_{t-1} | ~x_t | ~y_t | a_t]
    a_{t-1} & ~x_t & ~y_t -> a_t         [~a_{t-1} |  x_t |  y_t | a_t]

(a_{-1} = constant true, folded in; no auxiliary after the last position.)
a_t is only ever forced TRUE, never forced false, and setting each a_t to
its semantic value extends any x with x <=_lex y to a model, so the
projection onto (x, y) is exactly lex-<=.  Exhaustively unit-tested in
test_symmetry.py.  Fixed points of P are dropped from the chain: there
x_t = y_t identically, which is vacuous for <= and preserves the equality
prefix.

Everything is parameterized by the number of matched pairs (npairs=7 for
Conway-99) so the identical code path can be ground-truth-tested on the
srg(9,4,1,2) analogue (npairs=2), where the answer is fully known.
"""

import random
from functools import lru_cache
from itertools import combinations

NPAIRS_CONWAY = 7


# ---- the fixed combinatorial frame ---------------------------------------

@lru_cache(maxsize=None)
def matched_pairs(npairs=NPAIRS_CONWAY):
    """The fixed perfect matching on N(0) = {1..2n}: (1,2),(3,4),..."""
    return tuple((2 * a + 1, 2 * a + 2) for a in range(npairs))


@lru_cache(maxsize=None)
def outside_labels(npairs=NPAIRS_CONWAY):
    """Non-matched pairs of {1..2n} in lex order == encode.py's outside
    labels: outside vertex (2n+1)+i carries label outside_labels()[i]."""
    matched = set(matched_pairs(npairs))
    return tuple(p for p in combinations(range(1, 2 * npairs + 1), 2)
                 if p not in matched)


@lru_cache(maxsize=None)
def label_index(npairs=NPAIRS_CONWAY):
    return {p: i for i, p in enumerate(outside_labels(npairs))}


@lru_cache(maxsize=None)
def edge_positions(npairs=NPAIRS_CONWAY):
    """THE canonical order of the outside-edge variables: label-index pairs
    (u,v), u<v, row-major upper triangle.  All lex constraints and any
    future cube generation must use this same order."""
    n = len(outside_labels(npairs))
    return tuple((u, v) for u in range(n) for v in range(u + 1, n))


@lru_cache(maxsize=None)
def edge_index(npairs=NPAIRS_CONWAY):
    return {uv: t for t, uv in enumerate(edge_positions(npairs))}


# ---- group elements and induced actions ----------------------------------

def sigma_on_N(pi, signs, npairs=NPAIRS_CONWAY):
    """Permutation (dict) of {1..2n} from wreath element (pi, signs).

    pi: tuple with pi[a] = image pair of pair a (0-indexed pairs);
    signs: tuple of 0/1, signs[a] = 1 means pair a's members land swapped.
    Preserves the matching by construction, and every matching-preserving
    permutation of N(0) arises from exactly one (pi, signs), so these
    enumerate the full residual group."""
    m = {}
    for a in range(npairs):
        b = pi[a]
        x, y = 2 * b + 1, 2 * b + 2
        if signs[a]:
            x, y = y, x
        m[2 * a + 1] = x
        m[2 * a + 2] = y
    return m


def outside_perm(m_n, npairs=NPAIRS_CONWAY):
    """Induced permutation of label indices: label {a,b} -> {m(a),m(b)}."""
    idx = label_index(npairs)
    perm = []
    for a, b in outside_labels(npairs):
        x, y = m_n[a], m_n[b]
        if x > y:
            x, y = y, x
        perm.append(idx[(x, y)])   # image of a non-matched pair is non-matched
    assert sorted(perm) == list(range(len(perm))), 'induced map not a bijection'
    return perm


def edge_perm(p_out, npairs=NPAIRS_CONWAY):
    """Induced permutation P of edge positions: slot (u,v) -> slot of
    ({p(u),p(v)}).  The lex constraint for the element is X <=_lex X o P
    (positions read through P), over the edge_positions() order."""
    eidx = edge_index(npairs)
    P = []
    for u, v in edge_positions(npairs):
        x, y = p_out[u], p_out[v]
        if x > y:
            x, y = y, x
        P.append(eidx[(x, y)])
    return P


def element_edge_perm(pi, signs, npairs=NPAIRS_CONWAY):
    """Convenience: wreath element -> permutation of edge positions."""
    return edge_perm(outside_perm(sigma_on_N(pi, signs, npairs), npairs), npairs)


# ---- element sets for breaking -------------------------------------------

def structured_elements(npairs=NPAIRS_CONWAY):
    """Small-support involution-flavored elements (91 for npairs=7):
    the n single-pair flips, and for each of the C(n,2) pair transpositions
    all four sign patterns on the two moved pairs.  Small support means the
    lex chains hit moved positions early and propagate cheaply."""
    idp = tuple(range(npairs))
    els = []
    for a in range(npairs):
        s = [0] * npairs
        s[a] = 1
        els.append((idp, tuple(s)))
    for a in range(npairs):
        for b in range(a + 1, npairs):
            pi = list(idp)
            pi[a], pi[b] = pi[b], pi[a]
            pi = tuple(pi)
            for sa in (0, 1):
                for sb in (0, 1):
                    s = [0] * npairs
                    s[a], s[b] = sa, sb
                    els.append((pi, tuple(s)))
    return els


def random_elements(n, seed, npairs=NPAIRS_CONWAY):
    """n distinct non-identity elements sampled uniformly from the wreath
    group (uniform because (pi, signs) <-> group element is a bijection)."""
    rng = random.Random(seed)
    idp = tuple(range(npairs))
    seen = set()
    els = []
    while len(els) < n:
        pi = tuple(rng.sample(range(npairs), npairs))
        s = tuple(rng.randrange(2) for _ in range(npairs))
        if (pi, s) in seen or (pi == idp and not any(s)):
            continue
        seen.add((pi, s))
        els.append((pi, s))
    return els


def stab1_random_elements(n, seed, npairs=NPAIRS_CONWAY):
    """n distinct non-identity elements of the STABILIZER of matched pair 1
    (pi[0] == 0, order (npairs-1)!*2^npairs).  These permute S1 — the
    labels containing a member of pair 1, the first 12 in the canonical
    order — among themselves, so their lex constraints canonicalize the
    S1-matching cube space directly (the 10,395 matchings fall into just
    11 stabilizer orbits; see experiments/log.md 005).  Soundness: any
    subset of the group is sound, lexLeader_mixed_equisat."""
    rng = random.Random(seed)
    idp = tuple(range(npairs))
    seen = set()
    els = []
    while len(els) < n:
        rest = list(range(1, npairs))
        rng.shuffle(rest)
        pi = tuple([0] + rest)
        s = tuple(rng.randrange(2) for _ in range(npairs))
        if (pi, s) in seen or (pi == idp and not any(s)):
            continue
        seen.add((pi, s))
        els.append((pi, s))
    return els


# ---- CNF lex constraints -------------------------------------------------

def lex_le_clauses(xlits, ylits, next_aux):
    """Clauses for X <=_lex Y (generic: two equal-length literal lists).
    Returns (clauses, next_free_aux_var).  See module docstring."""
    assert len(xlits) == len(ylits)
    cls = []
    a_prev = 0                       # 0 = constant-true sentinel, folded in
    n = len(xlits)
    for t in range(n):
        x, y = xlits[t], ylits[t]
        pre = [] if a_prev == 0 else [-a_prev]
        cls.append(pre + [-x, y])
        if t == n - 1:
            break                    # no equality auxiliary after last position
        a = next_aux
        next_aux += 1
        cls.append(pre + [-x, -y, a])
        cls.append(pre + [x, y, a])
        a_prev = a
    return cls, next_aux


def lex_leader_clauses(xvars, P, next_aux, prefix=None, order=None):
    """Clauses for X <=_lex X o P, optionally truncated to the first
    `prefix` compared positions (sound, see module docstring).  Fixed
    points of P inside the window are dropped.

    `order` (default: identity = the canonical position order) is the
    sequence of position indices compared most-significant-first.  The
    soundness theorem (lean lexLeader_mixed_equisat) is order-agnostic —
    ANY single fixed order works — but ALL lex constraints within one
    instance must share the same order: lex-minima under different
    orders need not coincide, so mixing orders in one instance is
    UNSOUND.  Used by campaign.py's --sb-order s2first instances, where
    putting the S2-internal slots first lets stabilizer elements refute
    non-canonical S2-matchings by propagation (log 007)."""
    seq = range(len(P)) if order is None else order
    seq = list(seq) if prefix is None else list(seq)[:prefix]
    moved = [t for t in seq if P[t] != t]
    xl = [xvars[t] for t in moved]
    yl = [xvars[P[t]] for t in moved]
    return lex_le_clauses(xl, yl, next_aux)
