"""Independent exact checker for cert_n5_s1.json (N = 5 points on S^2, Coulomb s = 1).

Numbers in the certificate lie in K = Q(sqrt2, sqrt3), written [a, b, c, d] = a + b sqrt2 + c sqrt3 + d sqrt6. The
checker reads only the JSON and uses exact rational arithmetic throughout (sympy polynomial rings over QQ,
python-flint, Python fractions), with exact sign decisions in K and an exact principal-minor PSD test in the
uniqueness enumeration. It does not import the code that produced the certificate. It refuses to run with python -O.

Claim checked, with phi(t) = (2 - 2t)^(-1/2) and E(TBP) = 1/2 + 3 sqrt2 + sqrt3:
  (A) identity in K[u,v,t], checked as four identities in Q[u,v,t] (one per K-component; all structure is rational):
        (H(u)+H(v)+H(t))/3 - e/10 - R(u,v,t) = sum_r g_r z_r^T B_r z_r,  e = E(TBP),
      with R, S, Q_k, Sym, the reducers and the multipliers g_r exactly as in the s = 2 certificate;
  (B) each reduced matrix F'_k, B'_r (entries in K) is symmetric and positive definite. It is affine in
      (sqrt2, sqrt3, sqrt6), so it suffices that it is positive definite (exact leading minors) at the 8 corners of a
      rational box containing (sqrt2, sqrt3, sqrt6) (convexity of the positive definite cone);
  (C) H <= phi on [-1, 1) with equality exactly at -1, -1/2, 0: H > 0 on [-1, 1], and
      1 - (2-2t) H(t)^2 = (t+1)(2t+1)^2 t^2 q(t) with q > 0 on [-1, 1]; both positivity claims via exact Bernstein
      coefficients (exact subdivision) and exact signs in K;
  (D) uniqueness: equality forces every inner product into {-1, -1/2, 0}; among the 25 PSD rank <= 3 Gram matrices
      with such entries, energy E(TBP) occurs only for the 10 labellings of the TBP (exact comparisons in K).
The deduction from (A)-(D) to "E_1(x) >= E_1(TBP) for all 5 distinct points, with equality only for the TBP" is the
same as for s = 2 (see the README of the repository).
"""
import json, sys, itertools, time, math
from fractions import Fraction as Fr
from math import isqrt
from sympy import QQ, Matrix, Rational
from sympy.polys.rings import ring
from flint import fmpq_mat, fmpq

if not __debug__:
    raise SystemExit("assertions are disabled (python -O / PYTHONOPTIMIZE): refusing to run")
t0 = time.time()
C = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "cert_n5_s1.json"))
def Kf(z):                                                    # K element as 4 Fractions
    assert isinstance(z, list) and len(z) == 4, "K element must have exactly 4 components"
    return tuple(Fr(x) for x in z)

def ksign(z):
    def s2(x, y):                                             # sign of x + y sqrt2
        if x == 0 and y == 0: return 0
        if x >= 0 and y >= 0: return 1
        if x <= 0 and y <= 0: return -1
        dd = x * x - 2 * y * y
        return (1 if dd > 0 else -1) if x > 0 else (-1 if dd > 0 else 1)
    a, b, c, d = z
    sP, sQ = s2(a, b), s2(c, d)
    if sQ == 0: return sP
    if sP == 0: return sQ
    if sP == sQ: return sP
    s = s2(a * a + 2 * b * b - 3 * c * c - 6 * d * d, 2 * a * b - 6 * c * d)
    return s if sP > 0 else -s
def kmul(x, y):
    a, b, c, d = x; e, f, g, h = y
    return (a*e + 2*b*f + 3*c*g + 6*d*h, a*f + b*e + 3*c*h + 3*d*g, a*g + c*e + 2*b*h + 2*d*f, a*h + d*e + b*g + c*f)
kadd = lambda x, y: tuple(p + q for p, q in zip(x, y))
kscale = lambda x, r: tuple(p * r for p in x)
KZ = (Fr(0),) * 4

n = C["n"]; D = C["D"]; e = Kf(C["e"])
assert n == 5 and D == 10 and e == (Fr(1, 2), Fr(3), Fr(1), Fr(0))
assert len(C["H_chebyshev"]) == D + 1 and all(len(z) == 4 for z in C["H_chebyshev"])
assert len(C["F_reducers"]) == len(C["F_reduced"]) == 4
assert C["sos_degrees"] == [5, 4, 4, 4, 4, 4, 4, 3] and len(C["sos_reducers"]) == len(C["sos_reduced"]) == 8
def nmon(d): return len([m for m in itertools.product(range(d + 1), repeat=3) if sum(m) <= d])
for kk, (N, Fp) in enumerate(zip(C["F_reducers"], C["F_reduced"])):
    assert len(N) == D // 2 + 1 - kk and all(len(r) == len(Fp) for r in N) and all(len(r) == len(Fp) for r in Fp)
for dg, M, Bp in zip(C["sos_degrees"], C["sos_reducers"], C["sos_reduced"]):
    assert len(M) == nmon(dg) and all(len(r) == len(Bp) for r in M) and all(len(r) == len(Bp) for r in Bp)

# (B) positive definiteness via box corners
def sqrt_bounds(m, digits=60):
    Dd = 10 ** digits; r = isqrt(m * Dd * Dd); lo, hi = Fr(r, Dd), Fr(r + 1, Dd)
    assert lo * lo < m < hi * hi; return lo, hi
box = [sqrt_bounds(2), sqrt_bounds(3), sqrt_bounds(6)]
def pd_K(Mx):
    m = len(Mx); Mk = [[Kf(z) for z in row] for row in Mx]
    assert all(Mk[i][j] == Mk[j][i] for i in range(m) for j in range(i)), "matrix not symmetric"
    for th in itertools.product(*box):
        Q = fmpq_mat(m, m)
        for i in range(m):
            for j in range(m):
                z = Mk[i][j]; v = z[0] + th[0] * z[1] + th[1] * z[2] + th[2] * z[3]
                Q[i, j] = fmpq(v.numerator, v.denominator)
        if not all(fmpq_mat([[Q[i, j] for j in range(kk)] for i in range(kk)]).det() > 0 for kk in range(1, m + 1)):
            return False
    return True
for kk, Fp in enumerate(C["F_reduced"]): assert pd_K(Fp), f"F'_{kk} not PD"
for r, Bp in enumerate(C["sos_reduced"]): assert pd_K(Bp), f"B'_{r} not PD"
print(f"(B) all 4 F' and 8 B' blocks symmetric and positive definite (8 box corners each) ({time.time()-t0:.0f}s)", flush=True)

# (A) identity, one rational identity per K-component
R3, u, v, t = ring("u,v,t", QQ)
q = lambda x: QQ(Fr(x).numerator, Fr(x).denominator)
def cheb(j, x):
    a, b = R3(1), x
    if j == 0: return a
    for _ in range(j - 1): a, b = b, 2 * x * b - a
    return b
Qk = [R3(1), t - u * v]; W = (1 - u ** 2) * (1 - v ** 2)
while len(Qk) < 5: Qk.append(2 * (t - u * v) * Qk[-1] - W * Qk[-2])
def Sym(p):
    out = R3(0)
    for perm in itertools.permutations((u, v, t)): out += p.compose([(u, perm[0]), (v, perm[1]), (t, perm[2])])
    return out * QQ(1, 6)
def sub3(p, a, b, c): return p.compose([(u, a), (v, b), (t, c)])
gs = [R3(1), 1 + u, 1 + v, 1 + t, 1 - u, 1 - v, 1 - t, 1 + 2 * u * v * t - u ** 2 - v ** 2 - t ** 2]
symbase = {}
for comp in range(4):
    H = lambda x: sum((q(Kf(c)[comp]) * cheb(j, x) for j, c in enumerate(C["H_chebyshev"])), R3(0))
    S = R3(0)
    for kk, (N, Fp) in enumerate(zip(C["F_reducers"], C["F_reduced"])):
        Nm = [[q(x) for x in row] for row in N]; Fm = [[q(Kf(z)[comp]) for z in row] for row in Fp]
        m, rr = len(Nm), len(Fm)
        NF = [[sum((Nm[i][a] * Fm[a][j] for a in range(rr)), QQ(0)) for j in range(rr)] for i in range(m)]
        F = [[sum((NF[i][a] * Nm[j][a] for a in range(rr)), QQ(0)) for j in range(m)] for i in range(m)]
        for a in range(m):
            for b in range(m):
                if F[a][b] != 0:
                    if (kk, a, b) not in symbase: symbase[(kk, a, b)] = Sym(u ** a * v ** b * Qk[kk])
                    S += F[a][b] * symbase[(kk, a, b)]
    Rp = (n - 2) * S + sub3(S, u, u, R3(1)) + sub3(S, v, v, R3(1)) + sub3(S, t, t, R3(1)) + sub3(S, R3(1), R3(1), R3(1)) * QQ(1, n - 1)
    lhs = (H(u) + H(v) + H(t)) * QQ(1, 3) - q(e[comp]) * QQ(1, 10) - Rp
    rhs = R3(0)
    for g, dg, M, Bp in zip(gs, C["sos_degrees"], C["sos_reducers"], C["sos_reduced"]):
        mons = [mm for mm in itertools.product(range(dg + 1), repeat=3) if sum(mm) <= dg]
        Mm = [[q(x) for x in row] for row in M]; Bm = [[q(Kf(z)[comp]) for z in row] for row in Bp]
        rr = len(Bm)
        w = [sum((Mm[i][p] * (u ** mons[i][0] * v ** mons[i][1] * t ** mons[i][2]) for i in range(len(mons)) if Mm[i][p] != 0), R3(0)) for p in range(rr)]
        acc = R3(0)
        for p in range(rr):
            row = sum((Bm[p][qq] * w[qq] for qq in range(rr) if Bm[p][qq] != 0), R3(0))
            acc += w[p] * row
        rhs += g * acc
    assert lhs == rhs, f"identity fails in component {comp}"
print(f"(A) identity holds exactly in all four K-components ({time.time()-t0:.0f}s)", flush=True)

# (C) H <= phi
def cheb_mono(j):
    a, b = [Fr(1)], [Fr(0), Fr(1)]
    if j == 0: return a
    for _ in range(j - 1):
        c = [Fr(0)] + [2 * x for x in b]
        for i, x in enumerate(a): c[i] -= x
        a, b = b, c
    return b
Hm = [KZ] * (D + 1)
for j, c in enumerate(C["H_chebyshev"]):
    for a, m in enumerate(cheb_mono(j)): Hm[a] = kadd(Hm[a], kscale(Kf(c), m))
def pmul(p, r):
    o = [KZ] * (len(p) + len(r) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(r): o[i + j] = kadd(o[i + j], kmul(x, y))
    return o
pp = [kscale(z, -1) for z in pmul([(Fr(2), Fr(0), Fr(0), Fr(0)), (Fr(-2), Fr(0), Fr(0), Fr(0))], pmul(Hm, Hm))]
pp[0] = kadd(pp[0], (Fr(1), Fr(0), Fr(0), Fr(0)))
den = [Fr(0), Fr(0), Fr(1), Fr(5), Fr(8), Fr(4)]            # (t+1)(2t+1)^2 t^2 = t^2 + 5t^3 + 8t^4 + 4t^5
num = list(pp); quo = [KZ] * (len(num) - len(den) + 1)
for i in range(len(quo) - 1, -1, -1):
    c = kscale(num[i + len(den) - 1], Fr(1) / den[-1]); quo[i] = c
    for j, dv in enumerate(den): num[i + j] = kadd(num[i + j], kscale(c, -dv))
assert all(ksign(z) == 0 for z in num), "1-(2-2t)H^2 is not divisible by (t+1)(2t+1)^2 t^2"
def bern_pos(poly, a=Fr(-1), b=Fr(1), depth=0):
    nn = len(poly) - 1; sh = [KZ] * (nn + 1)
    for i, c in enumerate(poly):
        for j in range(i + 1): sh[j] = kadd(sh[j], kscale(c, math.comb(i, j) * a ** (i - j) * (b - a) ** j))
    bern = [KZ] * (nn + 1)
    for i in range(nn + 1):
        for j in range(i + 1): bern[i] = kadd(bern[i], kscale(sh[j], Fr(math.comb(i, j), math.comb(nn, j))))
    if all(ksign(z) > 0 for z in bern): return 1
    assert depth < 12, "positivity on [-1,1] not established"
    m = (a + b) / 2
    return bern_pos(poly, a, m, depth + 1) + bern_pos(poly, m, b, depth + 1)
nH, nq = bern_pos(Hm), bern_pos(quo)
print(f"(C) H > 0 on [-1,1] and 1-(2-2t)H^2 = (t+1)(2t+1)^2 t^2 q(t) with q > 0 on [-1,1] ({nH}, {nq} Bernstein intervals)", flush=True)

def psd_exact(G):
    """exact: a real symmetric matrix is PSD iff all its principal minors are >= 0."""
    m = G.shape[0]
    return all(G.extract(list(S_), list(S_)).det() >= 0 for r_ in range(1, m + 1) for S_ in itertools.combinations(range(m), r_))
# (D) uniqueness
vals = [Fr(-1), Fr(-1, 2), Fr(0)]; pairs = list(itertools.combinations(range(5), 2)); feas = 0; found = []
for combo in itertools.product(vals, repeat=10):
    G = Matrix(5, 5, lambda i, j: 1 if i == j else 0)
    for (i, j), c in zip(pairs, combo): G[i, j] = G[j, i] = Rational(c.numerator, c.denominator)
    if G.rank() > 3 or not psd_exact(G): continue
    feas += 1
    a_, b_, c_ = combo.count(Fr(-1)), combo.count(Fr(-1, 2)), combo.count(Fr(0))
    s = ksign((Fr(a_ - 1, 2), Fr(c_ - 6, 2), Fr(b_ - 3, 3), Fr(0)))   # E - E(TBP) = (a-1)/2 + (c-6)/sqrt2 + (b-3)/sqrt3
    assert s >= 0
    if s == 0: found.append(combo)
assert feas == 25 and len(found) == 10
for combo in found:
    G = dict(zip(pairs, combo)); anti = [p for p, c in G.items() if c == -1]; assert len(anti) == 1
    rest = [i for i in range(5) if i not in anti[0]]
    assert all(G[tuple(sorted(pq))] == Fr(-1, 2) for pq in itertools.combinations(rest, 2))
print(f"(D) {feas} PSD rank<=3 Gram matrices with entries in {{-1,-1/2,0}}; energy E(TBP) only for the {len(found)} TBP labellings ({time.time()-t0:.0f}s)")
print("CERTIFICATE VERIFIED")
