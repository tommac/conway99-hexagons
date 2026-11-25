#!/usr/bin/env python3
"""
transition.py — THREAD 1: the transition-system reformulation of srg(99,14,1,2).

Self-contained (stdlib only).  Shares NO code with encode.py / verify.py, so it
is an independent witness for every structural claim it checks.

WHAT IT PROVIDES
  * from-scratch constructions of the three ground-truth graphs
        Paley(9)          = srg(9,4,1,2)      (the ONLY known lambda=1,mu=2 graph)
        Kneser K(6,2)     = srg(15,6,1,3)     (lambda=1 only)
        cubic-surface     = srg(27,10,1,5)    (lambda=1 only)
    each verified against its parameter set before use;
  * root_local(G, x): the lambda=1 local decomposition at a vertex — the
    perfect matching on N(x), and for each a in N(x) the perfect matching
    M_a induced on a's outside neighbours;
  * for mu=2 graphs, the canonical labelling of the outside vertices by the
    non-matched pairs of N(x), the resulting TRANSITION SYSTEM on the
    cocktail-party graph K_{n x 2}, its circuits, and the "index-sharing"
    graph D on the outside vertices.

Run as a script: executes the full check battery and prints a report.
"""

from itertools import combinations


# --------------------------------------------------------------------------
# graphs, built from standard descriptions, then parameter-verified
# --------------------------------------------------------------------------

def make_graph(n, edges):
    adj = {i: set() for i in range(n)} if isinstance(n, int) else {u: set() for u in n}
    for u, v in edges:
        assert u != v
        adj[u].add(v)
        adj[v].add(u)
    return adj


def srg_params(adj):
    """Return (v,k,lam,mu) if adj is strongly regular, else raise."""
    vs = list(adj)
    v = len(vs)
    degs = {len(adj[u]) for u in vs}
    assert len(degs) == 1, f'not regular: degrees {sorted(degs)}'
    k = degs.pop()
    lams, mus = set(), set()
    for u, w in combinations(vs, 2):
        c = len(adj[u] & adj[w])
        (lams if w in adj[u] else mus).add(c)
    assert len(lams) == 1, f'lambda not constant: {sorted(lams)}'
    assert len(mus) == 1, f'mu not constant: {sorted(mus)}'
    return (v, k, lams.pop(), mus.pop())


def paley9():
    """Paley(9) = srg(9,4,1,2).  GF(9) = F_3[i], i^2 = -1; squares are the
    non-zero elements of the form s^2.  Vertices = field elements as pairs."""
    els = [(a, b) for a in range(3) for b in range(3)]          # a + b*i

    def mul(p, q):
        a, b = p
        c, d = q
        return ((a * c - b * d) % 3, (a * d + b * c) % 3)

    def sub(p, q):
        return ((p[0] - q[0]) % 3, (p[1] - q[1]) % 3)

    squares = {mul(p, p) for p in els if p != (0, 0)}
    assert len(squares) == 4, squares
    edges = [(u, w) for u, w in combinations(els, 2) if sub(u, w) in squares]
    return make_graph(els, edges)


def kneser62():
    """Complement of the triangular graph T(6): 2-subsets of {0..5}, adjacent
    iff disjoint.  = collinearity graph of GQ(2,2).  srg(15,6,1,3)."""
    vs = [frozenset(p) for p in combinations(range(6), 2)]
    edges = [(u, w) for u, w in combinations(vs, 2) if not (u & w)]
    return make_graph(vs, edges)


def cubic27():
    """The 27 lines on a cubic surface with 'meets' adjacency
    (= complement of the Schlaefli graph, = collinearity graph of GQ(2,4)).
    Lines a_i, b_i (i in 0..5) and c_ij (i<j).
      a_i meets b_j  iff i != j
      a_i meets c_jk iff i in {j,k}        (same for b_i)
      c_ij meets c_kl iff {i,j} disjoint from {k,l}
      a_i never meets a_j; b_i never meets b_j.
    srg(27,10,1,5)."""
    A = [('a', i) for i in range(6)]
    B = [('b', i) for i in range(6)]
    C = [('c', frozenset(p)) for p in combinations(range(6), 2)]
    vs = A + B + C

    def meets(u, w):
        (tu, iu), (tw, iw) = u, w
        if tu in 'ab' and tw in 'ab':
            return tu != tw and iu != iw
        if tu == 'c' and tw == 'c':
            return not (iu & iw)
        if tu == 'c':
            (tu, iu), (tw, iw) = (tw, iw), (tu, iu)
        return iu in iw                                     # a_i / b_i vs c_jk

    edges = [(u, w) for u, w in combinations(vs, 2) if meets(u, w)]
    return make_graph(vs, edges)


# --------------------------------------------------------------------------
# the lambda=1 local decomposition
# --------------------------------------------------------------------------

def perfect_matching_of(adj, S):
    """S must induce a 1-regular graph; return it as a dict v -> partner."""
    part = {}
    for u in S:
        nb = adj[u] & set(S)
        assert len(nb) == 1, f'{u} has {len(nb)} neighbours inside S, not 1'
        part[u] = next(iter(nb))
    for u in S:
        assert part[part[u]] == u
    return part


def root_local(adj, x):
    """lambda=1 local structure at x.

    Returns (N, partner, M) where
      N        = list of neighbours of x,
      partner  = the perfect matching N(x) induces (a -> a'),
      M        = {a: perfect matching on a's OUTSIDE neighbours}.
    Only uses lambda = 1 (every neighbourhood induces a perfect matching).
    """
    N = sorted(adj[x], key=repr)
    partner = perfect_matching_of(adj, N)
    M = {}
    for a in N:
        out = adj[a] - {x} - set(N)
        assert partner[a] in adj[a]
        M[a] = perfect_matching_of(adj, out)
    return N, partner, M


# --------------------------------------------------------------------------
# the mu=2 reformulation: outside vertices <-> edges of the cocktail-party
# graph, and the transition system
# --------------------------------------------------------------------------

def label_outside(adj, x, N):
    """mu=2 canonical labelling: outside vertex z -> frozenset(N(z) & N(x)).
    Asserts the labels are non-matched pairs and that the map is a bijection
    onto the 84-analogue set of non-matched pairs."""
    outside = [u for u in adj if u != x and u not in set(N)]
    lab = {}
    for z in outside:
        p = adj[z] & set(N)
        assert len(p) == 2, f'{z} has {len(p)} neighbours in N(x)'
        lab[z] = frozenset(p)
    assert len(set(lab.values())) == len(outside), 'labelling not injective'
    return lab


def cocktail_edges(N, partner):
    """Edges of K_{n x 2} on N: the non-matched pairs."""
    return [frozenset(p) for p in combinations(N, 2) if partner[p[0]] != p[1]]


def transition_system(adj, x):
    """Full mu=2 extraction.  Returns a dict with:
       N, partner, lab (vertex->pair), inv (pair->vertex),
       T: {a: matching on the 12 cocktail-neighbours of a}  (the transitions),
       D: the index-sharing graph on outside vertices (as adj dict),
       circuits: list of circuits of T, each a list of edges (frozensets).
    """
    N, partner, M = root_local(adj, x)
    lab = label_outside(adj, x, N)
    inv = {p: z for z, p in lab.items()}
    assert set(inv) == set(cocktail_edges(N, partner)), \
        'outside labels are not exactly the non-matched pairs'

    # transitions: M_a lives on a's outside neighbours; transport to N via labels
    T = {}
    for a in N:
        m = {}
        for z, w in M[a].items():
            b = next(iter(lab[z] - {a}))
            c = next(iter(lab[w] - {a}))
            m[b] = c
        assert set(m) == set(N) - {a, partner[a]}, 'M_a not supported on B_a'
        T[a] = m

    # index-sharing graph D on outside vertices
    D = {z: set() for z in lab}
    for a in N:
        for b, c in T[a].items():
            D[inv[frozenset((a, b))]].add(inv[frozenset((a, c))])
    for z in D:
        assert len(D[z]) == 2, f'D not 2-regular at {z}'
        for w in D[z]:
            assert z in D[w]

    circuits = _circuits(N, partner, T)
    return dict(N=N, partner=partner, lab=lab, inv=inv, T=T, D=D,
                circuits=circuits, M=M)


def _circuits(N, partner, T):
    """Decompose the edge set of K_{n x 2} into circuits of the transition
    system T: enter a vertex on edge {a,b}, leave on {a, T[a][b]}."""
    edges = set(cocktail_edges(N, partner))
    unused = set()
    for e in edges:                                  # arcs: (tail, head)
        u, w = tuple(e)
        unused.add((u, w))
        unused.add((w, u))
    circuits = []
    while unused:
        start = next(iter(unused))
        arc = start
        circ = []
        while True:
            u, w = arc                               # traverse edge {u,w} u->w
            circ.append(frozenset((u, w)))
            unused.discard((u, w))
            unused.discard((w, u))
            nxt = (w, T[w][u])                       # transition at w
            if frozenset(nxt) not in edges:
                raise AssertionError('bad transition')
            if (nxt[0], nxt[1]) not in unused and (nxt[1], nxt[0]) not in unused:
                break
            arc = nxt
        circuits.append(circ)
    assert sum(len(c) for c in circuits) == len(edges)
    return circuits


def cycles_of_2regular(D):
    """Cycle decomposition of a 2-regular graph given as adjacency dict."""
    seen, cycles = set(), []
    for s in D:
        if s in seen:
            continue
        cyc, prev, cur = [s], None, s
        seen.add(s)
        while True:
            nxts = [w for w in D[cur] if w != prev]
            nxt = nxts[0] if nxts else None
            if nxt is None or nxt == s:
                break
            cyc.append(nxt)
            seen.add(nxt)
            prev, cur = cur, nxt
        cycles.append(cyc)
    return cycles


# --------------------------------------------------------------------------
# check battery
# --------------------------------------------------------------------------

def _report(name, ok, detail=''):
    print(f'  [{"PASS" if ok else "FAIL"}] {name}' + (f'  — {detail}' if detail else ''))
    assert ok, name


def main():
    print('=== ground-truth graphs ===')
    G9, G15, G27 = paley9(), kneser62(), cubic27()
    for g, want in ((G9, (9, 4, 1, 2)), (G15, (15, 6, 1, 3)), (G27, (27, 10, 1, 5))):
        got = srg_params(g)
        _report(f'parameters {want}', got == want, f'computed {got}')

    print('\n=== lambda=1: every neighbourhood is a perfect matching (all 3 graphs) ===')
    for g, nm in ((G9, 'srg(9,4,1,2)'), (G15, 'srg(15,6,1,3)'), (G27, 'srg(27,10,1,5)')):
        ok = True
        for x in g:
            try:
                N, partner, M = root_local(g, x)
                assert len(M) == len(N)
            except AssertionError:
                ok = False
        _report(f'{nm}: N(x) = (k/2)K2 and each M_a a perfect matching, all roots',
                ok)

    print('\n=== mu=2 reformulation on Paley(9) (all 9 roots) ===')
    for x in G9:
        ts = transition_system(G9, x)
    ts = transition_system(G9, sorted(G9, key=repr)[0])
    _report('outside <-> edges of K_{2x2} bijection', len(ts['lab']) == 4)
    _report('transition system extracted at all 4 vertices of N(x)',
            all(len(m) == 2 for m in ts['T'].values()))
    circ = sorted(len(c) for c in ts['circuits'])
    _report('circuit type', circ == [4], f'circuit lengths {circ}')
    dcyc = sorted(len(c) for c in cycles_of_2regular(ts['D']))
    _report('D cycle type equals circuit type', dcyc == circ,
            f'D cycles {dcyc}')
    print('  circuit as edge sequence:',
          [tuple(sorted(e, key=repr)) for e in ts['circuits'][0]])

    print('\n=== Theorems B and C on Paley(9) (all 9 roots) ===')
    okB = okC1 = okC2 = True
    for x in G9:
        ts = transition_system(G9, x)
        adj, N, partner, lab = G9, ts['N'], ts['partner'], ts['lab']
        O = list(lab)
        # Theorem B: the bipartite graph N(a)&O -- N(a')&O is a perfect matching
        for a in N:
            A = [z for z in O if a in lab[z]]
            Ap = [z for z in O if partner[a] in lab[z]]
            if sorted(len(adj[z] & set(Ap)) for z in A) != [1] * len(A):
                okB = False
            if sorted(len(adj[z] & set(A)) for z in Ap) != [1] * len(Ap):
                okC1 = okC1 and False
        # Theorem C: a D-edge lies in no triangle inside O
        Dset = {frozenset((z, w)) for z in O for w in ts['D'][z]}
        for e in Dset:
            z, w = tuple(e)
            if adj[z] & adj[w] & set(O):
                okC2 = False
        # Theorem C: every other O-edge has its unique triangle inside O
        for z, w in combinations(O, 2):
            if w not in adj[z] or frozenset((z, w)) in Dset:
                continue
            if len(adj[z] & adj[w] & set(O)) != 1:
                okC2 = False
    _report('Thm B: N(a)&O -- N(a\')&O is a perfect matching', okB and okC1)
    _report('Thm C: D-edges lie in no O-triangle; other O-edges in exactly one',
            okC2)
    ts = transition_system(G9, sorted(G9, key=repr)[0])
    nD = sum(len(v) for v in ts['D'].values()) // 2
    nO = sum(len(G9[z] & set(ts['lab'])) for z in ts['lab']) // 2
    print(f'  |E(Gamma[O])| = {nO}, of which D-edges {nD}, '
          f'triads {(nO - nD) // 3}   '
          f'[Conway-99 analogue: 504 = 84 + 3*140]')


if __name__ == '__main__':
    main()
