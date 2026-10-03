"""Stage 2 of 2 for N = 5, Coulomb (s = 1): exact projection over K = Q(sqrt2, sqrt3), exact checks, certificate JSON.

Unknowns x in K^m are split into rational components x = x0 + x1 sqrt2 + x2 sqrt3 + x3 sqrt6. The constraint matrix
A is rational, so A x = b (b in K) splits into A x_i = b_i. Projection: least-norm correction of the rounded float
solution in each component; the real value of the total correction is tiny although the irrational components are not.
Checks:
  - every reduced Gram matrix is positive definite: it is affine in (sqrt2, sqrt3, sqrt6), so positive definiteness at
    the 8 corners of a tiny rational box around (sqrt2, sqrt3, sqrt6) implies it at the true point (convexity);
  - H <= phi = (2-2t)^(-1/2) on [-1,1): p = 1 - (2-2t) H^2 = (t+1)(2t+1)^2 t^2 q with q > 0 on [-1,1], shown by exact
    Bernstein coefficients (with exact subdivision) and exact signs in K; and H > 0 on [-1,1] the same way;
  - uniqueness enumeration with exact energies in K.
"""
import pickle, json, time, math, itertools, sys
from fractions import Fraction as Fr
import sympy as sy
from flint import fmpq_mat, fmpq, fmpz_mat
from kfield import k, add, sub, mul, scale, sign, to_float, sqrt_bounds, ZERO

t0 = time.time()
d = pickle.load(open('stage_s1.pkl', 'rb'))
A, bK, x0, nrow, ncol, cols = d['A'], d['bK'], d['x0'], d['nrow'], d['ncol'], d['cols']
D = 10
Am = fmpq_mat(nrow, ncol)
for i in range(nrow):
    for c, v in A[i].items(): Am[i, c] = fmpq(v.numerator, v.denominator)
rr, rank = Am.transpose().rref()
I = []
for i in range(rank):
    for c in range(nrow):
        if rr[i, c] != 0: I.append(c); break
S = 1
for i in I:
    for v in A[i].values(): S = S * v.denominator // math.gcd(S, v.denominator)
    for comp in range(4): S = S * bK[comp][i].denominator // math.gcd(S, bK[comp][i].denominator)
SH = 2 ** 50
X = [int(round(v * SH)) for v in x0]
xq = [Fr(v, SH) for v in X]
AiZ = fmpz_mat(len(I), ncol)
for a, i in enumerate(I):
    for c, v in A[i].items(): AiZ[a, c] = int(v * S)
Gq = fmpq_mat(AiZ * AiZ.transpose())
rhs = fmpq_mat(len(I), 4)
for a, i in enumerate(I):
    r0 = sum(v * xq[c] for c, v in A[i].items()) - bK[0][i]
    comps = [r0, -bK[1][i], -bK[2][i], -bK[3][i]]
    for j in range(4):
        rhs[a, j] = fmpq((comps[j] * S * S).numerator, (comps[j] * S * S).denominator)   # (Ai Ai^T) y = S^2 r
Y = Gq.solve(rhs)
print("rank", rank, "solved", f"({time.time()-t0:.1f}s)", flush=True)
comp = [list(xq), [Fr(0)] * ncol, [Fr(0)] * ncol, [Fr(0)] * ncol]
for j in range(4):
    yv = [Fr(int(Y[a, j].p), int(Y[a, j].q)) for a in range(len(I))]
    for a, i in enumerate(I):
        if yv[a] == 0: continue
        for c, v in A[i].items(): comp[j][c] -= v * yv[a]       # x_j -= A_I^T y_j   (A_I = Ai/S, y' = S y ... see below)
# note: (A_I A_I^T) y' = r  with A_I = Ai/S  <=>  (Ai Ai^T) y' = S^2 r ; correction = A_I^T y' = sum_i A[i] y'_i
bad = 0
for i in range(nrow):
    for j in range(4):
        if sum(v * comp[j][c] for c, v in A[i].items()) != bK[j][i]: bad += 1
assert bad == 0, f"exact system violated in {bad} component rows"
xK = [tuple(comp[j][c] for j in range(4)) for c in range(ncol)]
dev = max(abs(to_float(xK[c]) - x0[c]) for c in range(ncol))
print(f"exact system satisfied (all {nrow} rows x 4 components); max |x - x_float| = {dev:.2e} ({time.time()-t0:.1f}s)", flush=True)
pickle.dump(dict(xK=xK), open('stage2_s1.pkl', 'wb'))

# ---------------------------------------------------------------- positive definiteness by the box-corner argument
lo2, hi2 = sqrt_bounds(2); lo3, hi3 = sqrt_bounds(3); lo6, hi6 = sqrt_bounds(6)
def unpack(kind, blk):
    idx = [(ci, p, q) for ci, (kk, bb, p, q) in enumerate(cols) if kk == kind and bb == blk]
    m = max(max(p, q) for _, p, q in idx) + 1
    M = [[ZERO] * m for _ in range(m)]
    for ci, p, q in idx: M[p][q] = M[q][p] = xK[ci]
    return M
def pd_corners(M):
    m = len(M)
    for th in itertools.product((lo2, hi2), (lo3, hi3), (lo6, hi6)):
        Q = fmpq_mat(m, m)
        for i in range(m):
            for j in range(m):
                z = M[i][j]; v = z[0] + th[0] * z[1] + th[1] * z[2] + th[2] * z[3]
                Q[i, j] = fmpq(v.numerator, v.denominator)
        for kk in range(1, m + 1):
            if not (fmpq_mat([[Q[i, j] for j in range(kk)] for i in range(kk)]).det() > 0): return False
    return True
Fb = sorted({bb for kk, bb, p, q in cols if kk == "F"}); Bb = sorted({bb for kk, bb, p, q in cols if kk == "B"})
mats = {}
for kk_, blks in (("F", Fb), ("B", Bb)):
    for b_ in blks:
        M = unpack(kk_, b_); ok = pd_corners(M); mats[f"{kk_}{b_}"] = M
        print(f"  {kk_}{b_} (size {len(M)}): PD at all 8 corners: {ok}", flush=True)
        assert ok
print(f"positive definiteness: all blocks OK ({time.time()-t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- H <= phi on [-1, 1)
def cheb_mono(j):
    a, b = [Fr(1)], [Fr(0), Fr(1)]
    if j == 0: return a
    for _ in range(j - 1):
        c = [Fr(0)] + [2 * x for x in b]
        for i, x in enumerate(a): c[i] -= x
        a, b = b, c
    return b
H = [ZERO] * (D + 1)                      # monomial coefficients in K
for j in range(D + 1):
    for a_, c in enumerate(cheb_mono(j)):
        H[a_] = add(H[a_], scale(xK[j], c))
def pmulK(p, q):
    r = [ZERO] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i + j] = add(r[i + j], mul(x, y))
    return r
H2 = pmulK(H, H)
p = pmulK([k(2), k(-2)], H2); p = [scale(c, -1) for c in p]; p[0] = add(p[0], k(1))     # 1 - (2-2t) H^2
def divK(num, den):   # den rational coefficients (monomial, low->high)
    num = list(num); out = [ZERO] * (len(num) - len(den) + 1)
    for i in range(len(out) - 1, -1, -1):
        c = scale(num[i + len(den) - 1], Fr(1) / den[-1]); out[i] = c
        for j, dv in enumerate(den): num[i + j] = sub(num[i + j], scale(c, dv))
    assert all(sign(z) == 0 for z in num[:len(den) - 1]), "nonzero remainder"
    return out
den = [Fr(c) for c in sy.Poly(sy.expand((sy.Symbol('t') + 1) * (2 * sy.Symbol('t') + 1) ** 2 * sy.Symbol('t') ** 2), sy.Symbol('t')).all_coeffs()[::-1]]
q = divK(p, den)
def bernstein_positive(poly, a=Fr(-1), b=Fr(1), depth=0):
    """exact: all Bernstein coefficients of poly on [a, b] positive, else subdivide (max depth 12)."""
    n = len(poly) - 1
    # coefficients of poly(a + (b-a) x) in x
    sh = [ZERO] * (n + 1)
    for i, c in enumerate(poly):
        for j in range(i + 1):   # (a + (b-a)x)^i = sum C(i,j) a^(i-j) (b-a)^j x^j
            sh[j] = add(sh[j], scale(c, math.comb(i, j) * a ** (i - j) * (b - a) ** j))
    bern = [ZERO] * (n + 1)
    for i in range(n + 1):
        for j in range(i + 1):
            bern[i] = add(bern[i], scale(sh[j], Fr(math.comb(i, j), math.comb(n, j))))
    if all(sign(z) > 0 for z in bern): return 1
    assert depth < 12, "Bernstein positivity not established"
    m = (a + b) / 2
    return bernstein_positive(poly, a, m, depth + 1) + bernstein_positive(poly, m, b, depth + 1)
nq = bernstein_positive(q); nH = bernstein_positive(H)
print(f"H > 0 on [-1,1] ({nH} intervals) and q > 0 on [-1,1] ({nq} intervals): H <= phi with equality only at -1, -1/2, 0 "
      f"({time.time()-t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- uniqueness enumeration (energies in K)
vals = [Fr(-1), Fr(-1, 2), Fr(0)]; pairs = list(itertools.combinations(range(5), 2)); feas = 0; low = []
for combo in itertools.product(vals, repeat=10):
    G = sy.Matrix(5, 5, lambda i, j: 1 if i == j else 0)
    for (i, j), c in zip(pairs, combo): G[i, j] = G[j, i] = sy.Rational(c.numerator, c.denominator)
    if G.rank() > 3 or any(ev < 0 for ev in G.eigenvals(multiple=True)): continue
    feas += 1
    a_, b_, c_ = combo.count(Fr(-1)), combo.count(Fr(-1, 2)), combo.count(Fr(0))
    diff = k(Fr(a_ - 1, 2), Fr(c_ - 6, 2), Fr(b_ - 3, 3), 0)   # E - E(TBP) = (a-1)/2 + (c-6)/sqrt2 + (b-3)/sqrt3
    sgn = sign(diff)
    assert sgn >= 0, "a configuration below E(TBP)?!"
    if sgn == 0: low.append(combo)
assert feas == 25 and len(low) == 10
for combo in low:
    G = dict(zip(pairs, combo)); anti = [pp for pp, c in G.items() if c == -1]; assert len(anti) == 1
    rest = [i for i in range(5) if i not in anti[0]]
    assert all(G[tuple(sorted(pq))] == Fr(-1, 2) for pq in itertools.combinations(rest, 2))
print(f"uniqueness: {feas} feasible Gram matrices, energy E(TBP) only for the {len(low)} TBP labellings ({time.time()-t0:.1f}s)", flush=True)

def ks(z): return [f"{c.numerator}/{c.denominator}" if c.denominator != 1 else str(c.numerator) for c in z]
cert = dict(
    description=("N = 5 points on S^2, Coulomb (s = 1, phi(t) = (2-2t)^(-1/2)): exact three-point certificate over "
                 "K = Q(sqrt2, sqrt3); every number is [a, b, c, d] = a + b sqrt2 + c sqrt3 + d sqrt6. Same identity as the "
                 "s = 2 certificate with e = E(TBP) = 1/2 + 3 sqrt2 + sqrt3. AI-produced, not peer reviewed."),
    D=D, n=5, e=ks(k(Fr(1, 2), 3, 1, 0)), H_chebyshev=[ks(xK[j]) for j in range(D + 1)],
    F_reducers=d['Fred'], F_reduced=[[[ks(z) for z in row] for row in mats[f"F{b_}"]] for b_ in Fb],
    sos_g=["1", "1+u", "1+v", "1+t", "1-u", "1-v", "1-t", "detG=1+2uvt-u^2-v^2-t^2"], sos_degrees=[5, 4, 4, 4, 4, 4, 4, 3],
    sos_monomials="all (a,b,c) with a+b+c <= d, in itertools.product order",
    sos_reducers=d['SRED'], sos_reduced=[[[ks(z) for z in row] for row in mats[f"B{b_}"]] for b_ in Bb])
json.dump(cert, open('cert_n5_s1.json', 'w'))
import os; print("wrote cert_n5_s1.json", os.path.getsize('cert_n5_s1.json') // 1024, "KB", f"({time.time()-t0:.1f}s)")
