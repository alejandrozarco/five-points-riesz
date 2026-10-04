"""Stage 1 of 2 for odd s (N = 5; s = 1 is the Coulomb case; phi(t) = (2-2t)^(-s/2)): exact facial reduction at the
triangular bipyramid (TBP), float SDP in the reduced coordinates, and the exact linear system of the certificate, with
right-hand side in K = Q(sqrt2, sqrt3) stored as four rational components. Writes stage_s<s>.pkl.

Differences from 1_build_sdp.py (even s):
  - the touching conditions H = phi, H' = phi' at the TBP inner products are imposed only in the exact stage
    (NOTOUCH=1, the default): with irrational targets, Clarabel failed numerically when they were also float constraints;
  - every PSD block is written as Y + MU0*I with Y PSD (MU0 = 2e-7, the default). This gives numerical slack; positive
    definiteness after the exact projection is established by the exact box-corner checks of stage 2.
Next: 2c_exact_coulomb.py.
usage: RIESZ_S=1 POLYD=10 python3 1c_build_sdp_coulomb.py 4      (odd s from RIESZ_S, default 1; needs polyk.py here)
For odd s = 2M+1 all touching values and E(TBP) lie in K = Q(sqrt2, sqrt3); for s > 1 the sampled constraint is
H <= min(phi, 20 E(TBP) + 10), which is stronger, for conditioning (the s = 1 run is unchanged).
"""
import os
os.environ.setdefault("NOTOUCH", "1"); os.environ.setdefault("MU0", "2e-7")
import sys, os, json, itertools, time
from fractions import Fraction as Fr
import numpy as np
import sympy as sy
from flint import fmpq, fmpq_mat

D = int(os.environ.get("POLYD", "10"))
K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
n = 5; NPAIRS = 10
RS = int(os.environ.get("RIESZ_S", "1")); assert RS >= 1 and RS % 2 == 1, "odd s only"
MS = RS // 2                                   # s = 2 MS + 1
# E(TBP) = 2^-s + 6 * 2^(-s/2) + 3 * 3^(-s/2) = 2^-s + 6/2^(MS+1) sqrt2 + 3/3^(MS+1) sqrt3, as K-components
# (1, sqrt2, sqrt3, sqrt6); Coulomb (s = 1): 1/2 + 3 sqrt2 + sqrt3
E_TBP_K = (Fr(1, 2 ** RS), Fr(6, 2 ** (MS + 1)), Fr(3, 3 ** (MS + 1)), Fr(0))
SIZES = [D // 2 + 1 - k for k in range(K)]
DA = (D // 2, D // 2 - 1, D // 2 - 2)
half = Fr(1, 2)
GT = [[1, -1, 0, 0, 0], [-1, 1, 0, 0, 0], [0, 0, 1, -half, -half], [0, 0, -half, 1, -half], [0, 0, -half, -half, 1]]
GT = [[Fr(x) for x in r] for r in GT]

# ------------------------------------------------------------------ exact sparse polynomials in (u, v, t)
def P(d=None):
    return dict(d or {})
def padd(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + c * v
        if r[k] == 0: del r[k]
    return r
def pscale(p, c):
    return {k: c * v for k, v in p.items()} if c != 0 else {}
def pmul(p, q):
    r = {}
    for (a, b, c), x in p.items():
        for (d, e, f), y in q.items():
            k = (a + d, b + e, c + f); r[k] = r.get(k, 0) + x * y
    return {k: v for k, v in r.items() if v != 0}
def mono(a, b, c, x=1):
    return {(a, b, c): Fr(x)}
ONE = mono(0, 0, 0); U = mono(1, 0, 0); V = mono(0, 1, 0); T = mono(0, 0, 1)
def ppow(p, k):
    r = ONE
    for _ in range(k): r = pmul(r, p)
    return r
def peval(p, x):
    return sum(c * x[0] ** a * x[1] ** b * x[2] ** cc for (a, b, cc), c in p.items())
def ppermute(p, order):
    """q(x0,x1,x2) = p(x[order[0]], x[order[1]], x[order[2]])"""
    r = {}
    for e, c in p.items():
        ne = [0, 0, 0]
        for slot in range(3): ne[order[slot]] += e[slot]
        ne = tuple(ne); r[ne] = r.get(ne, 0) + c
    return r
def psym(p):
    r = {}
    for o in itertools.permutations(range(3)):
        r = padd(r, ppermute(p, o))
    return pscale(r, Fr(1, 6))
def psubst(p, spec):
    """spec[slot]: variable index (int) or constant (Fraction)."""
    r = {}
    for e, c in p.items():
        ne = [0, 0, 0]; coef = c
        for slot in range(3):
            s = spec[slot]
            if isinstance(s, int): ne[s] += e[slot]
            else: coef *= s ** e[slot]
        if coef != 0:
            ne = tuple(ne); r[ne] = r.get(ne, 0) + coef
    return {k: v for k, v in r.items() if v != 0}
def Qk(kmax):
    Q = [ONE, padd(T, pmul(U, V), -1)]
    W = pmul(padd(ONE, pmul(U, U), -1), padd(ONE, pmul(V, V), -1))
    while len(Q) <= kmax:
        Q.append(padd(pscale(pmul(padd(T, pmul(U, V), -1), Q[-1]), 2), pmul(W, Q[-2]), -1))
    return Q
QK = Qk(max(K, 1))
def cheb_mono(j):
    """monomial coefficients of T_j (exact ints)."""
    a, b = [Fr(1)], [Fr(0), Fr(1)]
    if j == 0: return a
    for _ in range(j - 1):
        c = [Fr(0)] + [2 * x for x in b]
        for i, x in enumerate(a): c[i] -= x
        a, b = b, c
    return b
def univ(coeffs, var):
    r = {}
    for i, c in enumerate(coeffs):
        if c != 0:
            e = [0, 0, 0]; e[var] = i; r[tuple(e)] = Fr(c)
    return r
def monos_upto(d):
    return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) <= d]
detG = padd(padd(padd(padd(ONE, pscale(pmul(pmul(U, V), T), 2)), pmul(U, U), -1), pmul(V, V), -1), pmul(T, T), -1)
BLOCKS = [("1", ONE, DA[0]), ("1+u", padd(ONE, U), DA[1]), ("1+v", padd(ONE, V), DA[1]), ("1+t", padd(ONE, T), DA[1]),
          ("1-u", padd(ONE, U, -1), DA[1]), ("1-v", padd(ONE, V, -1), DA[1]), ("1-t", padd(ONE, T, -1), DA[1]),
          ("detG", detG, DA[2])]

def nullspace_exact(rows, dim):
    if not rows: return sy.eye(dim)
    ns = sy.Matrix(rows).nullspace()
    cols = []
    for v in ns:
        den = sy.ilcm(*[sy.fraction(x)[1] for x in v]); cols.append(v * den)
    return sy.Matrix.hstack(*cols) if cols else sy.zeros(dim, 0)

# ------------------------------------------------------------------ 1. exact facial reduction
t0 = time.time()
Fred = []
for k, m in enumerate(SIZES):
    Z = [[Fr(0)] * m for _ in range(m)]
    for i in range(n):
        for j in range(n):
            for l in range(n):
                x = (GT[i][j], GT[i][l], GT[j][l]); q = peval(QK[k], x)
                if q == 0: continue
                for a in range(m):
                    for b in range(m):
                        Z[a][b] += x[0] ** a * x[1] ** b * q
    Fred.append(nullspace_exact([[sy.Rational(c.numerator, c.denominator) for c in r] for r in Z], m))
pts = sorted({(GT[i][j], GT[i][l], GT[j][l]) for i, j, l in itertools.permutations(range(n), 3)})
SRED = []
for name, g, d in BLOCKS:
    Z = monos_upto(d)
    rows = [[sy.Rational(*(lambda q: (q.numerator, q.denominator))(p[0] ** a * p[1] ** b * p[2] ** c)) for (a, b, c) in Z]
            for p in pts if peval(g, p) > 0]
    SRED.append(nullspace_exact(rows, len(Z)))
print("reduced F sizes", [M.shape[1] for M in Fred], "SOS sizes", [M.shape[1] for M in SRED], f"({time.time()-t0:.1f}s)", flush=True)

# ------------------------------------------------------------------ 2. float SDP in reduced coordinates
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cvxpy as cp
import polyk as pk
from numpy.polynomial import chebyshev as C
pr = pk.SOSProblem()
MU0 = float(os.environ.get("MU0", "0"))
if MU0 > 0:
    def _psd_shift(name, n_):
        Y = cp.Variable((n_, n_), PSD=True, name=name + "_y")
        X_ = Y + MU0 * np.eye(n_); pr.vars[name] = X_; return X_
    pr.psd = _psd_shift
sform = pk.LinPoly()
Fnames = []
for k, m in enumerate(SIZES):
    M = np.array(Fred[k], dtype=float)
    if M.shape[1] == 0: Fnames.append(None); continue
    pr.psd(f"F{k}", M.shape[1]); Fnames.append(f"F{k}")
    sform = sform + pk.LinPoly({f"F{k}": np.asarray(pk.SYM_AVG @ pk.Yk_columns(k, m) @ np.kron(M, M))})
R = (n - 2) * sform + sform.apply(pk.subst_matrix((0, 0, 1.0))) + sform.apply(pk.subst_matrix((1, 1, 1.0))) \
    + sform.apply(pk.subst_matrix((2, 2, 1.0))) + sform.apply(pk.subst_matrix((1.0, 1.0, 1.0))) * (1.0 / (n - 1))
pr.free("hc", D + 1); pr.free("e", 1)
Hsum = pk.LinPoly({"hc": (pk.univ_embed(0) + pk.univ_embed(1) + pk.univ_embed(2)) @ pk.cheb2mono() / 3.0})
slack = Hsum - R + pk.LinPoly({"e": -pk.pconst(1.0 / NPAIRS)[:, None]})
fblocks = [(pk.ONE, DA[0]), (pk.U + pk.ONE, DA[1]), (pk.V + pk.ONE, DA[1]), (pk.T + pk.ONE, DA[1]),
           (pk.ONE - pk.U, DA[1]), (pk.ONE - pk.V, DA[1]), (pk.ONE - pk.T, DA[1]),
           (pk.ONE + 2 * pk.pmul(pk.pmul(pk.U, pk.V), pk.T) - pk.pmul(pk.U, pk.U) - pk.pmul(pk.V, pk.V) - pk.pmul(pk.T, pk.T), DA[2])]
pr.add_identity(slack, fblocks, "slack", [np.array(M, dtype=float) for M in SRED])
hc = pr.vars["hc"]
def Hrow(t, j=0):
    return C.chebval(t, C.chebder(np.eye(D + 1), j) if j else np.eye(D + 1))
# phi(t) = (2-2t)^(-s/2), phi'(t) = s (2-2t)^(-s/2-1); s = 1: phi(-1)=1/2, phi(-1/2)=sqrt3/3, phi(0)=sqrt2/2,
# phi'(-1/2)=sqrt3/9, phi'(0)=sqrt2/4
TOUCH = [(-1.0, 0, (Fr(1, 2 ** RS), 0, 0, 0)), (-0.5, 0, (0, 0, Fr(1, 3 ** (MS + 1)), 0)), (0.0, 0, (0, Fr(1, 2 ** (MS + 1)), 0, 0)),
         (-0.5, 1, (0, 0, Fr(RS, 3 ** (MS + 2)), 0)), (0.0, 1, (0, Fr(RS, 2 ** (MS + 2)), 0, 0))]
KV = lambda c: float(c[0]) + float(c[1]) * 2 ** 0.5 + float(c[2]) * 3 ** 0.5 + float(c[3]) * 6 ** 0.5
for t, j, val in ([] if os.environ.get("NOTOUCH") else TOUCH):
    pr.cons.append(Hrow(t, j) @ hc == KV(val))
phi = lambda t: (2 - 2 * np.asarray(t, float)) ** (-RS / 2)
ts = pk.sample_grid(-1.0, 0.9999, 3000, [-1.0, -0.5, 0.0], 0.02)
fv = phi(ts)
if RS > 1: fv = np.minimum(fv, 20 * KV(E_TBP_K) + 10)    # H <= min(phi, cap) is stronger, so still valid; conditioning
pr.cons.append(C.chebvander(ts, D) @ hc <= fv)           # (s = 1 runs without the cap, as published)
OBJ = pr.vars["e"][0]
prob = pr.solve_rowreduced(OBJ, verbose=False, tol=1e-9)
xs = pr.xs()
print("float SDP:", prob.status, " e - E(TBP) =", float(xs["e"][0]) - KV(E_TBP_K), f"({time.time()-t0:.1f}s)", flush=True)

# ------------------------------------------------------------------ 3. exact linear system and projection
# unknowns: hc[0..D], then for each F block the upper triangle, then for each SOS block the upper triangle
cols = []      # (kind, block, p, q)
cols += [("h", None, j, None) for j in range(D + 1)]
for k, M in enumerate(Fred):
    for p in range(M.shape[1]):
        for q in range(p, M.shape[1]): cols.append(("F", k, p, q))
for r, M in enumerate(SRED):
    for p in range(M.shape[1]):
        for q in range(p, M.shape[1]): cols.append(("B", r, p, q))
print("unknowns:", len(cols), flush=True)

def tofr(M):
    return [[Fr(int(sy.fraction(x)[0]), int(sy.fraction(x)[1])) for x in M.row(i)] for i in range(M.shape[0])]
FredF = [tofr(M) for M in Fred]; SREDF = [tofr(M) for M in SRED]
# polynomial for each unknown (coefficient of the unknown in  slack - SOS ; identity:  sum = e/10 = (1/2 + 3*sqrt2 + sqrt3)/10)
Hcols = []
for j in range(D + 1):
    tj = cheb_mono(j)
    Hcols.append(pscale(padd(padd(univ(tj, 0), univ(tj, 1)), univ(tj, 2)), Fr(1, 3)))
def Rmap(s):
    return padd(padd(padd(padd(pscale(s, n - 2), psubst(s, (0, 0, Fr(1)))), psubst(s, (1, 1, Fr(1)))),
                     psubst(s, (2, 2, Fr(1)))), pscale(psubst(s, (Fr(1), Fr(1), Fr(1))), Fr(1, n - 1)))
Fcols = {}
for k, m in enumerate(SIZES):
    M = FredF[k]; mr = len(M[0]) if M else 0
    if mr == 0: continue
    base = {(a, b): psym(pmul(pmul(ppow(U, a), ppow(V, b)), QK[k])) for a in range(m) for b in range(m)}
    for p in range(mr):
        for q in range(p, mr):
            s = {}
            for a in range(m):
                for b in range(m):
                    c = M[a][p] * M[b][q] + (M[a][q] * M[b][p] if p != q else 0)
                    if c != 0: s = padd(s, base[(a, b)], c)
            Fcols[(k, p, q)] = Rmap(s)
print("F columns built", f"({time.time()-t0:.1f}s)", flush=True)
Bcols = {}
for r, (name, g, d) in enumerate(BLOCKS):
    Z = monos_upto(d); M = SREDF[r]; mr = len(M[0])
    w = []
    for p in range(mr):
        wp = {}
        for i, e in enumerate(Z):
            if M[i][p] != 0: wp[e] = wp.get(e, 0) + M[i][p]
        w.append(wp)
    gw = [pmul(g, wp) for wp in w]
    for p in range(mr):
        for q in range(p, mr):
            Bcols[(r, p, q)] = pscale(pmul(gw[p], w[q]), 1 if p == q else 2)
print("SOS columns built", f"({time.time()-t0:.1f}s)", flush=True)
ROWS = monos_upto(D)
ridx = {e: i for i, e in enumerate(ROWS)}
nrow = len(ROWS) + len(TOUCH); ncol = len(cols)
A = [dict() for _ in range(nrow)]   # sparse rows: col -> Fraction
def put(poly, ci, sign):
    for e, c in poly.items():
        assert e in ridx, ("degree overflow", e)
        A[ridx[e]][ci] = A[ridx[e]].get(ci, 0) + sign * c
for ci, (kind, blk, p, q) in enumerate(cols):
    if kind == "h": put(Hcols[p], ci, 1)
    elif kind == "F": put(Fcols[(blk, p, q)], ci, -1)
    else: put(Bcols[(blk, p, q)], ci, -1)
bK = [[Fr(0)] * nrow for _ in range(4)]
for comp in range(4): bK[comp][ridx[(0, 0, 0)]] = Fr(E_TBP_K[comp]) / NPAIRS
for i, (t, j, val) in enumerate(TOUCH):
    row = len(ROWS) + i
    for jj in range(D + 1):
        c = np.polynomial.chebyshev.Chebyshev.basis(jj)
        tm = cheb_mono(jj)
        der = [Fr(0)] * len(tm)
        if j == 0: v = sum(tm[a] * Fr(t).limit_denominator(4) ** a for a in range(len(tm)))
        else: v = sum(a * tm[a] * Fr(t).limit_denominator(4) ** (a - 1) for a in range(1, len(tm)))
        if v != 0: A[row][jj] = v
    for comp in range(4): bK[comp][row] = Fr(val[comp])
# float solution vector
x0 = []
for kind, blk, p, q in cols:
    if kind == "h": x0.append(float(xs["hc"][p]))
    elif kind == "F": X = xs[f"F{blk}"]; x0.append(float((X[p, q] + X[q, p]) / 2))
    else: X = xs[f"slack_B{blk}"]; x0.append(float((X[p, q] + X[q, p]) / 2))
xt = [Fr(v).limit_denominator(10 ** 14) for v in x0]
bf = [sum(float(bK[c][i]) * w for c, w in enumerate((1, 2 ** .5, 3 ** .5, 6 ** .5))) for i in range(nrow)]
res = [sum(float(c) * x0[ci] for ci, c in A[i].items()) - bf[i] for i in range(nrow)]
print("float residual max", max(abs(r) for r in res), f"({time.time()-t0:.1f}s)", flush=True)
import pickle
pickle.dump(dict(A=A, bK=bK, xt=xt, x0=x0, cols=cols, nrow=nrow, ncol=ncol, Fred=[[[str(v) for v in M.row(i)] for i in range(M.shape[0])] for M in Fred],
                 SRED=[[[str(v) for v in M.row(i)] for i in range(M.shape[0])] for M in SRED], TOUCH=[(t, j, [str(x) for x in v]) for t, j, v in TOUCH], RS=RS, D=D),
            open(f"stage_s{RS}.pkl", "wb"))
print(f"saved stage_s{RS}.pkl", flush=True)
