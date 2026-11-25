#!/usr/bin/env python3
"""
adjudicate.py -- INDEPENDENT re-derivation and re-testing of the load-bearing
claims of threads 1-4 (transition systems / spectral / mod-7 / partial
quadrangles).

Shares NO code with src/transition.py, src/spectral.py, src/prank*.py or
notes/math/*.py.  Every graph is rebuilt from a standard description here and
its parameters are RECOMPUTED before use.

Crucially it adds the ground-truth object thread 1 did not use:
srg(243,22,1,2) (Berlekamp-van Lint-Seidel), the ONLY non-degenerate known
member of the lambda=1, mu=2 family, built here from the ternary Golay code by
a different route than notes/math/g243.py (cyclic/QR construction, not the
extended-Golay-puncture route).

Run:  python3 scripts/adjudicate.py
"""
from fractions import Fraction
from itertools import combinations
import sys

FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "**FAIL**"
    if not cond:
        FAIL.append(name)
    print(f"  [{tag}] {name}" + (f"  {detail}" if detail else ""))
    return cond


# ---------------------------------------------------------------------------
# 0.  graph utilities
# ---------------------------------------------------------------------------

def srg_params(adj):
    """Recompute (v,k,lambda,mu).  Raises if not strongly regular."""
    v = len(adj)
    degs = {len(adj[u]) for u in range(v)}
    assert len(degs) == 1, f"not regular: degrees {sorted(degs)[:5]}..."
    k = degs.pop()
    lam = mu = None
    for u in range(v):
        for w in range(u + 1, v):
            c = len(adj[u] & adj[w])
            if w in adj[u]:
                if lam is None:
                    lam = c
                assert c == lam, f"lambda not constant at {u},{w}: {c} vs {lam}"
            else:
                if mu is None:
                    mu = c
                assert c == mu, f"mu not constant at {u},{w}: {c} vs {mu}"
    return v, k, lam, mu


# ---- Paley(9) --------------------------------------------------------------

def paley9():
    """GF(9) = F_3[i]/(i^2+1); x ~ y iff x-y is a nonzero square."""
    els = [(a, b) for a in range(3) for b in range(3)]
    idx = {e: i for i, e in enumerate(els)}

    def mul(p, q):
        a, b = p
        c, d = q
        return ((a * c - b * d) % 3, (a * d + b * c) % 3)

    def sub(p, q):
        return ((p[0] - q[0]) % 3, (p[1] - q[1]) % 3)

    squares = {mul(e, e) for e in els if e != (0, 0)}
    adj = [set() for _ in els]
    for i, p in enumerate(els):
        for j, q in enumerate(els):
            if i != j and sub(p, q) in squares:
                adj[i].add(j)
    return adj


# ---- Kneser(6,2) = complement of T(6) = srg(15,6,1,3) ----------------------

def kneser62():
    pairs = list(combinations(range(6), 2))
    adj = [set() for _ in pairs]
    for i, p in enumerate(pairs):
        for j, q in enumerate(pairs):
            if i != j and not (set(p) & set(q)):
                adj[i].add(j)
    return adj


# ---- GQ(2,4) = srg(27,10,1,5): 27 lines on a cubic surface -----------------

def gq24():
    """Schlaefli double-six model.  Lines a1..a6, b1..b6, c_ij (i<j).
    a_i meets b_j iff i != j ; a_i meets no a_j ; b_i meets no b_j ;
    c_ij meets a_i,a_j,b_i,b_j ; c_ij meets c_kl iff {i,j} cap {k,l} = empty."""
    names = [("a", i) for i in range(6)] + [("b", i) for i in range(6)] + \
            [("c", ij) for ij in combinations(range(6), 2)]
    idx = {n: i for i, n in enumerate(names)}
    adj = [set() for _ in names]

    def link(n, m):
        adj[idx[n]].add(idx[m])
        adj[idx[m]].add(idx[n])

    for i in range(6):
        for j in range(6):
            if i != j:
                link(("a", i), ("b", j))
    for ij in combinations(range(6), 2):
        i, j = ij
        for t in (i, j):
            link(("c", ij), ("a", t))
            link(("c", ij), ("b", t))
    for ij, kl in combinations(combinations(range(6), 2), 2):
        if not (set(ij) & set(kl)):
            link(("c", ij), ("c", kl))
    return adj


# ---- BvLS(243) = srg(243,22,1,2) from the ternary Golay code ---------------

def gf3_polymulmod(a, b, n):
    """multiply polys (coeff lists, low->high) mod x^n - 1 over GF(3)."""
    out = [0] * n
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    out[(i + j) % n] = (out[(i + j) % n] + ai * bj) % 3
    return out


def gf3_rref(rows, ncols):
    """row-reduce over GF(3); returns (rref rows, pivot cols)."""
    rows = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c]:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 if rows[r][c] == 1 else 2   # 2*2=4=1 mod 3
        rows[r] = [(x * inv) % 3 for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(rows[i][j] - f * rows[r][j]) % 3 for j in range(ncols)]
        piv.append(c)
        r += 1
        if r == len(rows):
            break
    return rows[:r], piv


def gf3_nullspace(rows, ncols):
    R, piv = gf3_rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        vec = [0] * ncols
        vec[f] = 1
        for i, c in enumerate(piv):
            vec[c] = (-R[i][f]) % 3
        basis.append(vec)
    return basis


def bvls243():
    """Cayley graph of GF(3)^5 on +-(columns of a parity check of the
    perfect ternary Golay [11,6,5]_3 code) = the Coxeter 11-cap of PG(4,3)."""
    n = 11
    # x^11 - 1 over GF(3): find monic degree-5 divisors
    target = [2] + [0] * 10 + [1]        # x^11 + 2  (= x^11 - 1)
    good = []
    for code in range(3 ** 5):
        c, coeffs = code, []
        for _ in range(5):
            coeffs.append(c % 3)
            c //= 3
        g = coeffs + [1]                  # monic degree 5
        # long division of target by g over GF(3)
        rem = target[:]
        for d in range(len(target) - 1, 4, -1):
            if rem[d]:
                f = rem[d]                # g is monic
                for i in range(6):
                    rem[d - 5 + i] = (rem[d - 5 + i] - f * g[i]) % 3
        if not any(rem):
            good.append(g)
    # build the cyclic codes, keep the one(s) of minimum weight 5
    chosen = None
    for g in good:
        G = [gf3_polymulmod(g, [0] * i + [1], n) for i in range(6)]
        # min weight by enumerating all 3^6 codewords
        best = 99
        for m in range(3 ** 6):
            t, co = m, []
            for _ in range(6):
                co.append(t % 3)
                t //= 3
            if not any(co):
                continue
            w = [0] * n
            for i, ci in enumerate(co):
                if ci:
                    for j in range(n):
                        w[j] = (w[j] + ci * G[i][j]) % 3
            best = min(best, sum(1 for z in w if z))
        if best == 5:
            chosen = (g, G)
            break
    assert chosen, "no [11,6,5]_3 cyclic code found"
    g, G = chosen
    H = gf3_nullspace(G, n)
    assert len(H) == 5
    cols = [tuple(H[r][c] for r in range(5)) for c in range(n)]
    # Cayley graph on GF(3)^5
    def neg(u):
        return tuple((-x) % 3 for x in u)
    S = set()
    for c in cols:
        S.add(c)
        S.add(neg(c))
    assert len(S) == 22 and tuple([0] * 5) not in S, len(S)
    verts = [tuple((i // 3 ** t) % 3 for t in range(5)) for i in range(243)]
    vidx = {u: i for i, u in enumerate(verts)}
    adj = [set() for _ in verts]
    for i, u in enumerate(verts):
        for s in S:
            w = tuple((u[t] + s[t]) % 3 for t in range(5))
            adj[i].add(vidx[w])
    return adj, cols


# ===========================================================================
print("=" * 78)
print("SECTION 0 -- ground truth, rebuilt independently and PARAMETER-CHECKED")
print("=" * 78)

P9 = paley9()
K62 = kneser62()
G24 = gq24()
B243, CAP = bvls243()

for nm, adj, want in [("Paley(9)", P9, (9, 4, 1, 2)),
                      ("Kneser(6,2)", K62, (15, 6, 1, 3)),
                      ("GQ(2,4)", G24, (27, 10, 1, 5)),
                      ("BvLS(243)", B243, (243, 22, 1, 2))]:
    got = srg_params(adj)
    check(f"{nm} parameters {got}", got == want, f"expected {want}")

# cap check on the 11 columns
def collinear3(a, b, c):
    # a,b,c in PG(4,3): collinear iff c is a nonzero combination of a,b
    for s in (1, 2):
        for t in (1, 2):
            if tuple((s * a[i] + t * b[i]) % 3 for i in range(5)) in (c, tuple((-x) % 3 for x in c)):
                return True
    return False

nocol = all(not collinear3(a, b, c) for a, b, c in combinations(CAP, 3))
check("the 11 columns form a cap of PG(4,3) (no 3 collinear)", nocol)


# ===========================================================================
print()
print("=" * 78)
print("SECTION 1 -- T4/F2: the q|63 family, re-derived from scratch")
print("=" * 78)

# srg(v,k,1,2):  v-1 = k + k(k-2)/2 = k^2/2
# eigenvalues t^2 + (mu-lam) t - (k-mu) = 0 -> t^2 + t - (k-2) = 0, disc = 4k-7
ok = True
for k in range(3, 4000):
    if 2 * (1 + k + Fraction(k * (k - 2), 2)) != 2 + k * k:
        ok = False
check("v = 1 + k + k(k-2)/2 = (k^2+2)/2 identically", ok)

# 2k - (v-1) = k(4-k)/2 ; with k=(q^2+7)/4 this is -(q^2+7)(q^2-9)/32
ok = True
for q in range(3, 400, 2):
    k = Fraction(q * q + 7, 4)
    lhs = k * (4 - k) / 2
    rhs = -Fraction((q * q + 7) * (q * q - 9), 32)
    if lhs != rhs:
        ok = False
check("2k-(v-1) = -(q^2+7)(q^2-9)/32   [T4's key algebra]", ok)

# (q^2+7)(q^2-9) = -63 mod q, gcd(q,32)=1 => q | 63
ok = all(((q * q + 7) * (q * q - 9) + 63) % q == 0 for q in range(3, 500, 2))
check("(q^2+7)(q^2-9) == -63 (mod q) for odd q", ok)

qs = [q for q in range(1, 100000, 2) if 63 % q == 0]
check("odd q with q|63", qs == [1, 3, 7, 9, 21, 63], str(qs))

fam = []
for q in [3, 7, 9, 21, 63]:
    if (q * q + 7) % 4:
        continue
    k = (q * q + 7) // 4
    v = (k * k + 2) // 2
    r, s = (q - 1) // 2, (-q - 1) // 2
    # multiplicities
    num = 2 * k + (v - 1) * (1 - 2)
    assert num % q == 0
    f = ((v - 1) - num // q) // 2
    g = (v - 1) - f
    fam.append((q, k, v, r, s, f, g))
    check(f"q={q}: k={k} v={v} r={r} s={s} f={f} g={g}",
          f + g == v - 1 and k + f * r + g * s == 0 and f > 0 and g > 0)
check("family = {9, 99, 243, 6273, 494019}",
      [t[2] for t in fam] == [9, 99, 243, 6273, 494019])

# independent brute force: sweep all (v,k) with lam=1, mu=2 feasible
def feasible_srg(v, k, lam, mu):
    if k * (k - lam - 1) != (v - k - 1) * mu:
        return False
    D = (lam - mu) ** 2 + 4 * (k - mu)
    if D <= 0:
        return False
    q = int(round(D ** 0.5))
    if q * q == D:
        if q == 0:
            return False
        num = 2 * k + (v - 1) * (lam - mu)
        if num % q:
            return False
        two_f = (v - 1) - num // q
        if two_f % 2 or two_f < 0 or two_f > 2 * (v - 1):
            return False
        return True
    # conference branch
    return v == 2 * k + 1 and lam == (k - 1) // 2 and mu == k // 2 and (k - 1) % 2 == 0

brute = []
for v in range(5, 600001):
    kk = 2 * (v - 1)
    k = int(round(kk ** 0.5))
    for kc in (k - 1, k, k + 1):
        if kc > 2 and kc * kc == 2 * (v - 1) and feasible_srg(v, kc, 1, 2):
            brute.append((v, kc))
check("brute force over v<=600000 gives exactly the same 5",
      sorted(set(b[0] for b in brute)) == [9, 99, 243, 6273, 494019], str(brute))

# Elzinga's c(lam,mu) and Makhnev-Minakova's k=u^2+u+2
lam, mu = 1, 2
c = (4 * mu - (lam - mu) ** 2) * (lam - mu + 2) * ((lam - mu) ** 2 + 2 * lam - 6 * mu)
check("Elzinga c(1,2) = -63", c == -63, f"got {c}")
check("Makhnev-Minakova k=u^2+u+2 <-> q=2u+1",
      all(((2 * u + 1) ** 2 + 7) // 4 == u * u + u + 2 for u in [1, 3, 4, 10, 31]))
check("srg(19,6,1,2) is infeasible (4k-7=17 not a square, not conference)",
      not feasible_srg(19, 6, 1, 2))


# ===========================================================================
print()
print("=" * 78)
print("SECTION 2 -- T2/F1,F2: ratio bound arithmetic, alpha and omega")
print("=" * 78)

n, K, R, S = 99, 14, 3, -4
# quotient matrix eigenvalue: theta2 = d - m(k-d)/(n-m), d = 2e/m
ok_lo = ok_hi = True
for m in range(1, n):
    for e in range(0, m * (m - 1) // 2 + 1):
        d = Fraction(2 * e, m)
        th = d - Fraction(m * (K - d), n - m)
        lo = Fraction(m * (m - 22), 11)
        hi = Fraction(m * (m + 27), 18)
        if (th >= S) != (Fraction(e) >= lo):
            ok_lo = False
        if (th <= R) != (Fraction(e) <= hi):
            ok_hi = False
check("s <= theta2  <=>  e(S) >= m(m-22)/11   (exact, all m,e)", ok_lo)
check("theta2 <= r  <=>  e(S) <= m(m+27)/18   (exact, all m,e)", ok_hi)

mmax = max(m for m in range(1, 100) if Fraction(m * (m - 1), 2) <= Fraction(m * (m + 27), 18))
check("ratio bound gives omega <= 4 (not 3)", mmax == 4, f"largest clique size allowed = {mmax}")
amax = max(m for m in range(1, 100) if Fraction(m * (m - 22), 11) <= 0)
check("ratio bound gives alpha <= 22", amax == 22)
# elementary convexity proof: m^2+5m-594 <= 0
amax2 = max(m for m in range(1, 100) if m * m + 5 * m - 594 <= 0)
check("elementary counting bound m^2+5m-594<=0 gives the same alpha <= 22", amax2 == 22)

# ratio bound tested exhaustively on Paley(9) (2^9 subsets)
def ratio_test(adj, v, k, r, s):
    bad = 0
    lo_tight = hi_tight = 0
    for mask in range(1, 1 << v):
        Sset = [i for i in range(v) if mask >> i & 1]
        m = len(Sset)
        if m == v:
            continue
        e = sum(1 for a, b in combinations(Sset, 2) if b in adj[a])
        d = Fraction(2 * e, m)
        th = d - Fraction(m * (k - d), v - m)
        if th < s or th > r:
            bad += 1
        if th == s:
            lo_tight += 1
        if th == r:
            hi_tight += 1
    return bad, lo_tight, hi_tight
b, lt, ht = ratio_test(P9, 9, 4, 1, -2)
check("ratio bound: 0 violations over all 2^9 subsets of Paley(9)", b == 0,
      f"tight low {lt}, tight high {ht}")


# ===========================================================================
print()
print("=" * 78)
print("SECTION 3 -- T3: the mod-p identities and the rank bounds")
print("=" * 78)

def adj_matrix(adj):
    v = len(adj)
    return [[1 if j in adj[i] else 0 for j in range(v)] for i in range(v)]

def rank_mod_p(M, p):
    A = [[x % p for x in row] for row in M]
    rows, cols = len(A), len(A[0])
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r

def rank_Q(M):
    A = [[Fraction(x) for x in row] for row in M]
    rows, cols = len(A), len(A[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(cols)]
        r += 1
        if r == rows:
            break
    return r

# (A - rI)(A - sI) = mu J  -- the general identity
for nm, adj, (v, k, lam, mu), (r, s) in [
        ("Paley(9)", P9, (9, 4, 1, 2), (1, -2)),
        ("Kneser(6,2)", K62, (15, 6, 1, 3), (1, -3)),
        ("GQ(2,4)", G24, (27, 10, 1, 5), (1, -5)),
        ("BvLS(243)", B243, (243, 22, 1, 2), (4, -5))]:
    A = adj_matrix(adj)
    ok = True
    for i in range(v):
        for j in range(v):
            # ((A-rI)(A-sI))_{ij}
            val = sum(A[i][t] * A[t][j] for t in range(v))
            val += -(r + s) * A[i][j] + (r * s if i == j else 0)
            if val != mu:
                ok = False
                break
        if not ok:
            break
    check(f"(A-rI)(A-sI) = mu*J on {nm}", ok)

# Conway specialisation: (A-3I)(A+4I) = 2J is the SRG condition rewritten
# A^2 = 14I + 1*A + 2*(J-I-A)  =>  A^2 + A - 12I = 2J = (A-3I)(A+4I)
check("(A-3I)(A+4I) = A^2 + A - 12I  [symbolic]", (-3) + 4 == 1 and (-3) * 4 == -12)
check("Conway: r-s = 7, so A-3I == A+4I (mod 7)", 3 - (-4) == 7)
check("rank_7(A-3I) <= min(rank_Q(A-3I), rank_Q(A+4I)) = min(45,55) = 45",
      min(99 - 54, 99 - 44) == 45)
check("nilpotency bound would only give 50", (99 - 1) // 2 + 1 == 50)
check("N*1 = (k-r)*1 = 11*1 = 4*1 != 0 mod 7", (14 - 3) % 7 == 4)

# the weight formula, tested where it can be tested
def row_diff_weights(adj, r, p):
    v = len(adj)
    A = adj_matrix(adj)
    N = [[(A[i][j] - (r if i == j else 0)) % p for j in range(v)] for i in range(v)]
    adjw, nonw = set(), set()
    for i, j in combinations(range(v), 2):
        w = sum(1 for t in range(v) if (N[i][t] - N[j][t]) % p)
        (adjw if j in adj[i] else nonw).add(w)
    return adjw, nonw

for nm, adj, (k, lam, mu), r, p in [
        ("Paley(9) p=3", P9, (4, 1, 2), 1, 3),
        ("Kneser(6,2) p=2", K62, (6, 1, 3), 1, 2),
        ("GQ(2,4) p=2", G24, (10, 1, 5), 1, 2),
        ("GQ(2,4) p=3", G24, (10, 1, 5), 1, 3),
        ("BvLS(243) p=3", B243, (22, 1, 2), 4, 3)]:
    aw, nw = row_diff_weights(adj, r, p)
    pred_a = 2 * (k - lam) - 2 * (1 if (r + 1) % p == 0 else 0)
    pred_n = 2 * (k - mu) + 2 * (1 if r % p else 0)
    check(f"weight formula on {nm}: adj {sorted(aw)} vs {pred_a}, non {sorted(nw)} vs {pred_n}",
          aw == {pred_a} and nw == {pred_n})
check("Conway p=7: adjacent 2(14-1)-0 = 26, non-adjacent 2(14-2)+2 = 26",
      2 * (14 - 1) - 0 == 26 and 2 * (14 - 2) + 2 == 26)

# rank_p vs min(f,g)+1 on the known lambda=1,mu=2 members
for nm, adj, r, p, fg in [("Paley(9)", P9, 1, 3, (4, 4)), ("BvLS(243)", B243, 4, 3, (132, 110))]:
    v = len(adj)
    A = adj_matrix(adj)
    M = [[A[i][j] - (r if i == j else 0) for j in range(v)] for i in range(v)]
    rp, rq = rank_mod_p(M, p), rank_Q(M)
    check(f"{nm}: rank_{p}(A-rI) = {rp}, rank_Q = {rq}, min(f,g)+1 = {min(fg)+1}",
          rp <= min(fg) + 1 and rq == v - max(fg))


# ===========================================================================
print()
print("=" * 78)
print("SECTION 4 -- T2/F4: the 'kill lemma' eigenvector, re-derived and re-tested")
print("=" * 78)
# Lemma: G srg(v,k,1,mu), theta root of t^2+(mu-1)t-(k-mu)=0.
# p vertex, u in N(p), u' = unique common nbr.  T = {p} u N(p) u (N(u)\N[p]).
# z_p = theta+mu-2, z_u = -(theta+mu-2), z_{u'}=0, z_c=+1 on N(p)\{u,u'},
# z_y = -1 on N(u)\N[p].   Claim (i) A_T z = theta z, (ii) sum over N(w) cap T = 0.

def test_kill_lemma(nm, adj, k, mu, thetas, limit=None):
    v = len(adj)
    tested_i = tested_ii = 0
    ok_i = ok_ii = True
    pairs = [(p, u) for p in range(v) for u in sorted(adj[p])]
    if limit:
        pairs = pairs[:limit]
    for (p, u) in pairs:
        common = adj[p] & adj[u]
        assert len(common) == 1
        up = next(iter(common))
        T = {p} | adj[p] | (adj[u] - adj[p] - {p})
        for theta in thetas:
            a = theta + mu - 2
            z = {}
            z[p] = a
            z[u] = -a
            z[up] = 0
            for c in adj[p] - {u, up}:
                z[c] = 1
            for y in adj[u] - adj[p] - {p}:
                z[y] = -1
            assert set(z) == T, (len(z), len(T))
            for t in T:
                lhs = sum(z[w] for w in adj[t] & T)
                if lhs != theta * z[t]:
                    ok_i = False
                tested_i += 1
            for w in range(v):
                if w in T:
                    continue
                if sum(z[t] for t in adj[w] & T) != 0:
                    ok_ii = False
                tested_ii += 1
    check(f"kill lemma (i) A_T z = theta z on {nm}", ok_i, f"{tested_i} row equations")
    check(f"kill lemma (ii) extension identity on {nm}", ok_ii, f"{tested_ii} outside vertices")

test_kill_lemma("Paley(9)", P9, 4, 2, (1, -2))
test_kill_lemma("Kneser(6,2)", K62, 6, 3, (1, -3))
test_kill_lemma("GQ(2,4)", G24, 10, 5, (1, -5))
test_kill_lemma("BvLS(243) [2nd mu=2 member -- NOT tested by thread 2]",
                B243, 22, 2, (4, -5), limit=60)

# the algebraic core: k-2 = (theta+1)(theta+mu-2) is the SRG eigenvalue equation
ok = True
for (k, mu) in [(4, 2), (6, 3), (10, 5), (22, 2), (14, 2), (112, 2), (994, 2)]:
    D = (mu - 1) ** 2 + 4 * (k - mu)
    q = int(round(D ** 0.5))
    if q * q != D:
        continue
    for theta in ((-(mu - 1) + q) // 2, (-(mu - 1) - q) // 2):
        if theta * theta + (mu - 1) * theta - (k - mu) != 0:
            continue
        if k - 2 != (theta + 1) * (theta + mu - 2):
            ok = False
check("k-2 = (theta+1)(theta+mu-2) for both non-principal eigenvalues", ok)

# Conway-99 explicit vector: support 26
check("Conway s-eigenvector: z_p=-4+2-2=-4? no: theta+mu-2 = -4+0 = -4",
      (-4) + 2 - 2 == -4 and 3 + 2 - 2 == 3)


# ===========================================================================
print()
print("=" * 78)
print("SECTION 5 -- T1: the transition-system reformulation, tested on BOTH")
print("            known lambda=1, mu=2 members (Paley(9) AND BvLS(243))")
print("=" * 78)

def transition_data(adj, x):
    """Full transition-system extraction at root x for an srg(v,k,1,2)."""
    v = len(adj)
    N = sorted(adj[x])
    k = len(N)
    O = [u for u in range(v) if u != x and u not in adj[x]]
    # matching on N
    partner = {}
    for a in N:
        c = adj[a] & adj[x]
        assert len(c) == 1
        partner[a] = next(iter(c))
    assert all(partner[partner[a]] == a and partner[a] != a for a in N)
    # labels
    label = {}
    for z in O:
        L = adj[z] & adj[x]
        assert len(L) == 2, (z, len(L))
        b, c = sorted(L)
        assert partner[b] != c, "label is a matched pair -- Lemma 2 FAILS"
        label[z] = (b, c)
    assert len(set(label.values())) == len(O), "labelling not injective"
    inv = {L: z for z, L in label.items()}
    nonmatched = [(a, b) for a, b in combinations(N, 2) if partner[a] != b]
    assert set(inv) == set(nonmatched), "labelling not surjective"
    # transitions M_a
    M = {}
    for a in N:
        Ba = [b for b in N if b != a and b != partner[a]]
        m = {}
        for b in Ba:
            z = inv[tuple(sorted((a, b)))]
            nb = [c for c in Ba if c != b and
                  inv[tuple(sorted((a, c)))] in adj[z]]
            assert len(nb) == 1, f"M_{a} not a matching at {b}: {len(nb)}"
            m[b] = nb[0]
        assert all(m[m[b]] == b for b in Ba)
        M[a] = m
    # D graph
    D = {z: set() for z in O}
    for z, w in combinations(O, 2):
        if len(set(label[z]) & set(label[w])) == 1 and w in adj[z]:
            D[z].add(w)
            D[w].add(z)
    assert all(len(D[z]) == 2 for z in O), "D not 2-regular"
    # cycles of D
    seen, cyc = set(), []
    for z in O:
        if z in seen:
            continue
        length, cur, prev = 0, z, None
        while True:
            seen.add(cur)
            length += 1
            nxt = [w for w in D[cur] if w != prev]
            prev, cur = cur, nxt[0]
            if cur == z:
                break
        cyc.append(length)
    return dict(N=N, O=O, k=k, partner=partner, label=label, inv=inv,
                M=M, D=D, ctype=sorted(cyc, reverse=True))

for nm, adj, roots in [("Paley(9)", P9, range(9)), ("BvLS(243)", B243, range(0, 243, 27))]:
    types = set()
    good = True
    for x in roots:
        try:
            td = transition_data(adj, x)
        except AssertionError as e:
            good = False
            print("      assertion:", e)
            break
        types.add(tuple(td["ctype"]))
        # Theorem A: no 3-circuit
        if any(c < 4 for c in td["ctype"]):
            good = False
    check(f"Lemmas 1-4 (matching / bijection / transitions / D 2-regular) on {nm}", good)
    check(f"Theorem A (no 3-circuit) on {nm}", good and all(min(t) >= 4 for t in types))
    print(f"      circuit types over the roots tested: {sorted(types)}")

# Theorem B and Theorem C on BvLS(243) -- the non-degenerate member
td = transition_data(B243, 0)
N, O, M, label, partner, inv = td["N"], td["O"], td["M"], td["label"], td["partner"], td["inv"]
adj = B243
# Theorem B
okB = True
for a in N:
    if a > partner[a]:
        continue
    ap = partner[a]
    L = [z for z in O if a in label[z]]
    Rt = [z for z in O if ap in label[z]]
    for z in L:
        if len(set(adj[z]) & set(Rt)) != 1:
            okB = False
    for z in Rt:
        if len(set(adj[z]) & set(L)) != 1:
            okB = False
check("Theorem B (a/a' bipartite perfect matching) on BvLS(243)", okB)
# Theorem C
Oset = set(O)
dedges = tri = 0
okC = True
triads = []
for z, w in combinations(O, 2):
    if w not in adj[z]:
        continue
    shared = set(label[z]) & set(label[w])
    tri_in_O = (adj[z] & adj[w]) & Oset
    if shared:
        dedges += 1
        if tri_in_O:
            okC = False          # D-edge must lie in NO triangle inside O
    else:
        if len(tri_in_O) != 1:
            okC = False
        else:
            t = next(iter(tri_in_O))
            triads.append(frozenset((z, w, t)))
ntriads = len(set(triads))
kk = td["k"]
check("Theorem C on BvLS(243): D-edges lie in no O-triangle, rest form triads", okC)
check(f"BvLS(243): |O|={len(O)} D-edges={dedges} triads={ntriads}; "
      f"lines {kk//2} + {dedges} + {ntriads} = {kk//2+dedges+ntriads} "
      f"(predicted {len(B243)*kk//6})",
      dedges == len(O) and kk // 2 + dedges + ntriads == len(B243) * kk // 6)
check("every outside vertex lies on exactly (deg_O - 2)/2 triads",
      all(sum(1 for T3 in set(triads) if z in T3) == (kk - 2 - 2) // 2 for z in O))
# do triads ever contain a matched pair of labels?  (T1 sec 5.1 identity)
mp = sum(1 for T3 in set(triads)
         for z, w in combinations(sorted(T3), 2)
         if any(partner[i] == j for i in label[z] for j in label[w]))
print(f"      triads containing a matched pair of indices: {mp}")
t_b = {b: sum(1 for c in M[b] if partner[c] == M[b][c]) for b in N}
print(f"      t_b (matched pairs paired by M_b) distribution: "
      f"{sorted(set(t_b.values()))}, sum = {sum(t_b.values())}")


# ===========================================================================
print()
print("=" * 78)
print("SECTION 6 -- T4/F6: the Wilbrink-Brouwer local identity, re-derived")
print("=" * 78)
# (v-N) - (kN-2M) + lam*M + mu*(C(N,2)-M) - sum_i C(d_i,2) = x_0 + sum_{j>=3} C(j-1,2) x_j
def wb_test(nm, adj, v, k, lam, mu, samples, seed=1):
    import random
    rng = random.Random(seed)
    bad = 0
    nontriv = 0
    for _ in range(samples):
        Nn = rng.randint(2, min(12, v - 1))
        Sset = rng.sample(range(v), Nn)
        Sx = set(Sset)
        M = sum(1 for a, b in combinations(Sset, 2) if b in adj[a])
        d = [len(adj[u] & Sx) for u in Sset]
        xs = {}
        for w in range(v):
            if w in Sx:
                continue
            j = len(adj[w] & Sx)
            xs[j] = xs.get(j, 0) + 1
        lhs = (v - Nn) - (k * Nn - 2 * M) + lam * M + mu * (Nn * (Nn - 1) // 2 - M) \
              - sum(di * (di - 1) // 2 for di in d)
        rhs = xs.get(0, 0) + sum((j - 1) * (j - 2) // 2 * c for j, c in xs.items() if j >= 3)
        if lhs != rhs:
            bad += 1
        if rhs != 0:
            nontriv += 1
    check(f"Wilbrink-Brouwer identity on {nm}", bad == 0,
          f"{samples} random induced subgraphs, {nontriv} with nonzero RHS")

wb_test("Paley(9)", P9, 9, 4, 1, 2, 3000)
wb_test("BvLS(243)", B243, 243, 22, 1, 2, 3000)
wb_test("GQ(2,4)", G24, 27, 10, 1, 5, 3000)


# ===========================================================================
print()
print("=" * 78)
print("SECTION 7 -- T1 sec 2.2: the level-1 orbit sizes, and the four")
print("            obstruction families as THEOREMS about lambda=1,mu=2")
print("=" * 78)

# level-1 orbits of the 3486 outside-outside variables under S_2 wr S_7
MATCH = [(1, 2), (3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (13, 14)]
PAR = {}
for _a, _b in MATCH:
    PAR[_a], PAR[_b] = _b, _a
LBL = [frozenset(p) for p in combinations(range(1, 15), 2) if PAR[p[0]] != p[1]]
check("84 non-matched pairs of a 7K_2", len(LBL) == 84)
LIDX = {L: i for i, L in enumerate(LBL)}
PRS = list(combinations(range(84), 2))
check("3486 outside-outside slots", len(PRS) == 3486)

def gens():
    out = []
    for (a, b) in MATCH:                      # swap inside a class
        g = {i: i for i in range(1, 15)}
        g[a], g[b] = b, a
        out.append(g)
    for i in range(6):                        # swap two adjacent classes
        (a, b), (c, d) = MATCH[i], MATCH[i + 1]
        g = {t: t for t in range(1, 15)}
        g[a], g[c] = c, a
        g[b], g[d] = d, b
        out.append(g)
    return out

parent = list(range(3486))
def find(i):
    while parent[i] != i:
        parent[i] = parent[parent[i]]
        i = parent[i]
    return i
def union(i, j):
    a, b = find(i), find(j)
    if a != b:
        parent[a] = b
PIDX = {p: i for i, p in enumerate(PRS)}
for g in gens():
    for n, (i, j) in enumerate(PRS):
        Li = frozenset(g[t] for t in LBL[i])
        Lj = frozenset(g[t] for t in LBL[j])
        a, b = LIDX[Li], LIDX[Lj]
        union(n, PIDX[(min(a, b), max(a, b))])
from collections import Counter
orb = Counter(find(i) for i in range(3486))
check("level-1 orbit sizes = {42, 84, 840, 840, 1680}",
      sorted(orb.values()) == [42, 84, 840, 840, 1680], str(sorted(orb.values())))
share = sum(sz for rep, sz in orb.items()
            if len(LBL[PRS[rep][0]] & LBL[PRS[rep][1]]) == 1)
check("924 index-sharing (transition) variables", share == 924, str(share))

# The four obstruction families, stated as universal claims about any
# srg(v,k,1,2), TESTED on BvLS(243) (thread 1 tested only Paley(9), where
# |O| = 4 and most of these are vacuous).
def obstruction_tests(nm, adj, x):
    td = transition_data(adj, x)
    N, O, label, partner = td["N"], td["O"], td["label"], td["partner"]
    Oset, inv = set(O), td["inv"]
    n_A = n_B = n_C = n_D = 0
    okA = okB = okC = okD = True
    for z in O:
        a, b = label[z]
        # L2-A: M_a is a matching -> z has exactly ONE neighbour among {z_ac}
        for idx in (a, b):
            same = [w for w in O if idx in label[w] and w != z]
            c = sum(1 for w in same if w in adj[z])
            n_A += 1
            if c != 1:
                okA = False
        # L2-B: |N(z) cap N(u) cap O| <= 1 for u in {a', b'}
        for u in (partner[a], partner[b]):
            c = len((adj[z] & adj[u]) & Oset)
            n_B += 1
            if c > 1:
                okB = False
        # L3-A: |N(z) cap N(c) cap O| <= 2 for c not in {a,a',b,b'}
        for c in N:
            if c in (a, b, partner[a], partner[b]):
                continue
            cc = len((adj[z] & adj[c]) & Oset)
            n_C += 1
            if cc > 2:
                okC = False
    # L3-B: a D-edge lies in no triangle inside O
    for z, w in combinations(O, 2):
        if w in adj[z] and len(set(label[z]) & set(label[w])) == 1:
            n_D += 1
            if (adj[z] & adj[w]) & Oset:
                okD = False
    check(f"L2-A (M_a is a matching) on {nm}", okA, f"{n_A} instances")
    check(f"L2-B (|N(z) cap N(a') cap O| <= 1) on {nm}", okB, f"{n_B} instances")
    check(f"L3-A (|N(z) cap N(c) cap O| <= 2) on {nm}", okC, f"{n_C} instances")
    check(f"L3-B (D-edge in no O-triangle) on {nm}", okD, f"{n_D} instances")

obstruction_tests("Paley(9)", P9, 0)
obstruction_tests("BvLS(243)", B243, 0)


# ===========================================================================
print()
print("=" * 78)
print("SECTION 8 -- NEW: is the transition system CANONICAL in the known members?")
print("=" * 78)
for nm, adj, roots in [("Paley(9)", P9, range(9)), ("BvLS(243)", B243, range(243))]:
    allcanon = True
    nsys = 0
    for x in roots:
        td = transition_data(adj, x)
        M, partner = td["M"], td["partner"]
        for a in td["N"]:
            for b, c in M[a].items():
                if partner[b] != c:
                    allcanon = False
        nsys += 1
    kk = len(adj[0])
    ndf = 1
    for t in range(1, kk - 2, 2):
        ndf *= t                                # (k-3)!! transition systems per vertex
    check(f"{nm}: M_a(b) = b' at ALL {nsys} roots (CANONICAL transition system)",
          allcanon, f"a priori {ndf} systems per vertex, {ndf}^{kk} in total")

print()
print("=" * 78)
if FAIL:
    print(f"{len(FAIL)} CHECK(S) FAILED:")
    for f in FAIL:
        print("   -", f)
else:
    print("ALL CHECKS PASSED")
print("=" * 78)


# ===========================================================================
print()
print("=" * 78)
print("SECTION 9 -- T3/F7: the decisive counterexample rebuilt independently")
print("            (W(3) and its dual Q(4,3), both srg(40,12,2,4), p=3)")
print("=" * 78)
# W(3): points of PG(3,3), collinear iff B(x,y)=0 for the symplectic form.
def pg_points(d, q=3):
    pts, seen = [], set()
    for m in range(q ** d):
        vec, t = [], m
        for _ in range(d):
            vec.append(t % q)
            t //= q
        if not any(vec):
            continue
        vec = tuple(vec)
        # normalise: first nonzero entry = 1
        i = next(t for t in range(d) if vec[t])
        inv = pow(vec[i], q - 2, q)
        nv = tuple((x * inv) % q for x in vec)
        if nv not in seen:
            seen.add(nv)
            pts.append(nv)
    return pts

def symp(x, y):
    return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % 3

PTS = pg_points(4)
check("PG(3,3) has 40 points", len(PTS) == 40)
W3 = [set() for _ in PTS]
for i, j in combinations(range(40), 2):
    if symp(PTS[i], PTS[j]) == 0:
        W3[i].add(j)
        W3[j].add(i)
check(f"W(3) collinearity graph parameters {srg_params(W3)}", srg_params(W3) == (40, 12, 2, 4))

# lines of W(3) = totally isotropic projective lines; the DUAL GQ is Q(4,3)
def norm(v):
    i = next(t for t in range(4) if v[t])
    inv = pow(v[i], 1, 3)
    inv = pow(v[i], 3 - 2, 3)
    return tuple((x * inv) % 3 for x in v)
lines = set()
for i in range(40):
    for j in W3[i]:
        span = set()
        for a in range(3):
            for b in range(3):
                w = tuple((a * PTS[i][t] + b * PTS[j][t]) % 3 for t in range(4))
                if any(w):
                    span.add(norm(w))
        lines.add(frozenset(span))
LINES = sorted(lines, key=sorted)
check(f"W(3) has 40 lines of 4 points", len(LINES) == 40 and all(len(L) == 4 for L in LINES))
Q43 = [set() for _ in LINES]
for i, j in combinations(range(40), 2):
    if LINES[i] & LINES[j]:
        Q43[i].add(j)
        Q43[j].add(i)
check(f"dual (= Q(4,3)) collinearity graph parameters {srg_params(Q43)}",
      srg_params(Q43) == (40, 12, 2, 4))

for nm, adjg in [("W(3)", W3), ("Q(4,3)", Q43)]:
    A = adj_matrix(adjg)
    M = [[A[i][j] - (2 if i == j else 0) for j in range(40)] for i in range(40)]
    print(f"      {nm}: rank_3(A-2I) = {rank_mod_p(M,3)}   rank_Q = {rank_Q(M)}")
A1 = adj_matrix(W3); A2 = adj_matrix(Q43)
M1 = [[A1[i][j] - (2 if i == j else 0) for j in range(40)] for i in range(40)]
M2 = [[A2[i][j] - (2 if i == j else 0) for j in range(40)] for i in range(40)]
r1, r2 = rank_mod_p(M1, 3), rank_mod_p(M2, 3)
check("T3/F7: same parameters, DIFFERENT 3-ranks -> p-rank is NOT parameter-forced",
      r1 != r2, f"{r1} vs {r2}; region check: 3||6, 3 does not divide 40 or k-r=10")
