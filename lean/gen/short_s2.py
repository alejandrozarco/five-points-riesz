#!/usr/bin/env python3
"""Short exact re-rounding of the N = 5, s = 2 three-point certificate (for Lean).

Input: stage.pkl of construction/1_build_sdp.py (float SDP solution in facially reduced coordinates, reducers).
Output: cert_n5_s2_short.json in the format of cert_n5_s2.json (so check/check_n5_even.py verifies it unchanged, with s = 2),
with every number short (dyadic times small 2,3,5-smooth factors), plus LDL^T + diagonally dominant remainder data
for every reduced block (field "psd").

Method (the idea of the short re-rounding used for the seven-point s = 2 certificate in alejandrozarco/thomson-n7-log,
specialised to the untyped identity):
  * reducers N are normalised to echelon form: in each column the last non-zero entry is 1 and that row ("free row")
    is zero in all other columns. monos_upto(d) is in lex order, a monomial order, so every SOS generator
    G = c * g_r * w_a * w_b  (w = N^T z, c = 1 if a = b else 2) has lex-leading monomial LM(g_r) z_f(a) z_f(b) and
    leading coefficient +-1 or +-2;
  * for each monomial one generator with that leading monomial is DESIGNATED (g = 1 block and diagonal preferred);
    the normal form NF (reduction by designated generators in decreasing lex order) divides only by +-1, +-2;
  * stage 1: the LHS unknowns (H Chebyshev coefficients, kernel blocks F') solve the non-designated equations
    NF(L(x) - SOS(B'_rounded)) = 0 together with the five touching pins, by Gauss-Jordan with greedy smooth pivots;
    the other LHS unknowns stay at their 2^-K roundings;
  * stage 2: the residual L(x) - SOS(B'_rounded) is reduced by the designated generators and the reduction
    coefficients are added to the designated reduced Gram entries; the remainder is exactly 0;
  * PSD data: float LDL^T of M - eps I, L rounded to 2^-52, d to 2^-60, exact DD check of the remainder.
usage: python3 short_s2.py <stage.pkl> [K=40] [out=cert_n5_s2_short.json]
"""
import sys, json, pickle, itertools, time
from fractions import Fraction as Fr
from math import lcm
import numpy as np

T0 = time.time()
def log(*a): print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)

stage = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 40
OUT = sys.argv[3] if len(sys.argv) > 3 else "cert_n5_s2_short.json"
d = pickle.load(open(stage, "rb"))
cols, x0 = d["cols"], d["x0"]
D = 10; n = 5; E = Fr(17, 4)

# ---------------------------------------------------------------- exact polynomials (dict (a,b,c) -> Fraction)
def padd(p, q, c=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + c * v
        if r[k] == 0: del r[k]
    return r
def pscale(p, c): return {k: c * v for k, v in p.items()} if c != 0 else {}
def pmul(p, q):
    r = {}
    for (a, b, c), x in p.items():
        for (e, f, g), y in q.items():
            k = (a + e, b + f, c + g); r[k] = r.get(k, 0) + x * y
    return {k: v for k, v in r.items() if v != 0}
ONE = {(0, 0, 0): Fr(1)}; U = {(1, 0, 0): Fr(1)}; V = {(0, 1, 0): Fr(1)}; T = {(0, 0, 1): Fr(1)}
def ppow(p, k):
    r = ONE
    for _ in range(k): r = pmul(r, p)
    return r
def perm(p, o):
    r = {}
    for e, c in p.items():
        ne = [0, 0, 0]
        for s in range(3): ne[o[s]] += e[s]
        ne = tuple(ne); r[ne] = r.get(ne, 0) + c
    return r
def psym(p):
    r = {}
    for o in itertools.permutations(range(3)): r = padd(r, perm(p, o))
    return pscale(r, Fr(1, 6))
def psub(p, spec):
    r = {}
    for e, c in p.items():
        ne = [0, 0, 0]; cc = c
        for s in range(3):
            if isinstance(spec[s], int): ne[spec[s]] += e[s]
            else: cc *= spec[s] ** e[s]
        if cc != 0:
            ne = tuple(ne); r[ne] = r.get(ne, 0) + cc
    return {k: v for k, v in r.items() if v != 0}
def cheb(j):
    a, b = [Fr(1)], [Fr(0), Fr(1)]
    if j == 0: return a
    for _ in range(j - 1):
        c = [Fr(0)] + [2 * x for x in b]
        for i, x in enumerate(a): c[i] -= x
        a, b = b, c
    return b
def univ(coefs, var):
    r = {}
    for i, c in enumerate(coefs):
        if c != 0:
            e = [0, 0, 0]; e[var] = i; r[tuple(e)] = Fr(c)
    return r
def monos(dd): return [e for e in itertools.product(range(dd + 1), repeat=3) if sum(e) <= dd]
Q = [ONE, padd(T, pmul(U, V), -1)]; Wp = pmul(padd(ONE, pmul(U, U), -1), padd(ONE, pmul(V, V), -1))
while len(Q) < 6: Q.append(padd(pscale(pmul(padd(T, pmul(U, V), -1), Q[-1]), 2), pmul(Wp, Q[-2]), -1))
detG = padd(padd(padd(padd(ONE, pscale(pmul(pmul(U, V), T), 2)), pmul(U, U), -1), pmul(V, V), -1), pmul(T, T), -1)
GS = [ONE, padd(ONE, U), padd(ONE, V), padd(ONE, T), padd(ONE, U, -1), padd(ONE, V, -1), padd(ONE, T, -1), detG]
DEG = [5, 4, 4, 4, 4, 4, 4, 3]
def Rmap(s):
    return padd(padd(padd(padd(pscale(s, n - 2), psub(s, (0, 0, Fr(1)))), psub(s, (1, 1, Fr(1)))), psub(s, (2, 2, Fr(1)))),
                pscale(psub(s, (Fr(1), Fr(1), Fr(1))), Fr(1, n - 1)))
def LM(p): return max(p)

# ---------------------------------------------------------------- reducers in echelon form; coordinate change
def normalise(Mstr):
    M = [[Fr(x) for x in row] for row in Mstr]; m, r = len(M), len(M[0])
    free, scale = [], []
    for c in range(r):
        f = max(i for i in range(m) if M[i][c] != 0); free.append(f); scale.append(M[f][c])
    N = [[M[i][c] / scale[c] for c in range(r)] for i in range(m)]
    for c in range(r):
        assert N[free[c]][c] == 1 and all(N[free[c]][cc] == 0 for cc in range(r) if cc != c)
        assert all(N[i][c] == 0 for i in range(free[c] + 1, m))
    return N, free, scale      # old coords B_old = N_old B'_old N_old^T = N (S B'_old S) N^T: B'_new = S B'_old S
Fn = [normalise(M) for M in d["Fred"]]; Sn = [normalise(M) for M in d["SRED"]]
def old_block(kind, blk):
    idx = [(ci, p, q) for ci, (kk, bb, p, q) in enumerate(cols) if kk == kind and bb == blk]
    m = max(max(p, q) for _, p, q in idx) + 1; Mx = np.zeros((m, m))
    for ci, p, q in idx: Mx[p, q] = Mx[q, p] = x0[ci]
    return Mx
hc0 = [x0[ci] for ci, (kk, bb, p, q) in enumerate(cols) if kk == "h"]
Ff = [np.outer(sc, sc) * old_block("F", k) for k, (_, _, sc) in enumerate(Fn)]
Bf = [np.outer(sc, sc) * old_block("B", r) for r, (_, _, sc) in enumerate(Sn)]
sc = lambda v: np.array([float(x) for x in v])
Ff = [np.outer(sc(s), sc(s)) * old_block("F", k) for k, (_, _, s) in enumerate(Fn)]
Bf = [np.outer(sc(s), sc(s)) * old_block("B", r) for r, (_, _, s) in enumerate(Sn)]
log("normalised reducers; min eig F':", [f"{np.linalg.eigvalsh(M)[0]:.2e}" for M in Ff],
    "B':", [f"{np.linalg.eigvalsh(M)[0]:.2e}" for M in Bf])

# ---------------------------------------------------------------- LHS columns and SOS generators
mon5 = {dd: monos(dd) for dd in set(DEG)}
Hcols = [pscale(padd(padd(univ(cheb(j), 0), univ(cheb(j), 1)), univ(cheb(j), 2)), Fr(1, 3)) for j in range(D + 1)]
LHSvars, LHScols = [], []
for j in range(D + 1): LHSvars.append(("h", j, None)); LHScols.append(Hcols[j])
for k, (N, free, _) in enumerate(Fn):
    m = len(N); r = len(N[0])
    base = {(a, b): psym(pmul(pmul(ppow(U, a), ppow(V, b)), Q[k])) for a in range(m) for b in range(m)}
    for p in range(r):
        for q in range(p, r):
            s = {}
            for a in range(m):
                for b in range(m):
                    c = N[a][p] * N[b][q] + (N[a][q] * N[b][p] if p != q else 0)
                    if c != 0: s = padd(s, base[(a, b)], c)
            LHSvars.append(("F", k, (p, q))); LHScols.append(pscale(Rmap(s), -1))
L0 = {(0, 0, 0): -E / 10}
gens = {}     # (r, p, q) -> polynomial (including factor 2 off-diagonal)
for r_, (N, free, _) in enumerate(Sn):
    Z = mon5[DEG[r_]]; w = []
    for p in range(len(N[0])):
        wp = {}
        for i, e in enumerate(Z):
            if N[i][p] != 0: wp[e] = wp.get(e, 0) + N[i][p]
        w.append(wp)
    gw = [pmul(GS[r_], wp) for wp in w]
    for p in range(len(w)):
        for q in range(p, len(w)):
            gens[(r_, p, q)] = pscale(pmul(gw[p], w[q]), 1 if p == q else 2)
log("LHS unknowns", len(LHSvars), " SOS generators", len(gens))

# designation
cand = {}
for key, G in gens.items():
    m = LM(G); c = G[m]
    r_, p, q = key
    pref = (0 if r_ == 0 else 1, 0 if p == q else 1, abs(c))
    if m not in cand or pref < cand[m][0]: cand[m] = (pref, key, c)
ALL = sorted(monos(D), reverse=True)
desig = {m: (cand[m][1], cand[m][2]) for m in ALL if m in cand}
nondes = [m for m in ALL if m not in desig]
log("monomials", len(ALL), " designated", len(desig), " non-designated", len(nondes), nondes[:12])
assert all(abs(c) in (1, 2) for _, c in desig.values())

def NF(p, record=None):
    p = dict(p)
    for m in ALL:
        c = p.get(m, 0)
        if c == 0 or m not in desig: continue
        key, lc = desig[m]; delta = c / lc
        if record is not None: record[key] = record.get(key, 0) + delta
        p = padd(p, gens[key], -delta)
    return p

# ---------------------------------------------------------------- rounding
def rnd(x): return Fr(round(x * (1 << K)), 1 << K)
xL = {}
for (kind, a, b) in LHSvars:
    xL[(kind, a, b)] = rnd(hc0[a]) if kind == "h" else rnd(Ff[a][b[0], b[1]])
Bq = {key: rnd(Bf[key[0]][key[1], key[2]]) for key in gens}
SOSr = {}
for key, G in gens.items():
    if Bq[key] != 0: SOSr = padd(SOSr, G, Bq[key])
log("rounded; building stage 1")

# ---------------------------------------------------------------- stage 1
NFcols = [NF(c) for c in LHScols]; NFL0 = NF(L0)
rows, rhs = [], []
for m in nondes:
    rows.append([c.get(m, 0) for c in NFcols]); rhs.append(-NFL0.get(m, 0))   # NF(L(x)) - sum_extra B NF(G) = 0
pins = [(-1, 0, Fr(1, 4)), (Fr(-1, 2), 0, Fr(1, 3)), (0, 0, Fr(1, 2)), (Fr(-1, 2), 1, Fr(2, 9)), (0, 1, Fr(1, 2))]
for t0, der, val in pins:
    row = [Fr(0)] * len(LHSvars)
    for j in range(D + 1):
        cj = cheb(j)
        row[j] = sum(cj[a] * Fr(t0) ** a for a in range(len(cj))) if der == 0 else \
                 sum(a * cj[a] * Fr(t0) ** (a - 1) for a in range(1, len(cj)))
    rows.append(row); rhs.append(val)
# extra stage-1 unknowns: non-designated SOS generator entries (their NF lives on non-designated monomials)
desig_keys = {key for key, _ in desig.values()}
extra = [key for key in gens if key not in desig_keys]
log("computing NF of", len(extra), "non-designated generators")
NFextra = [NF(gens[key]) for key in extra]
for i, m in enumerate(nondes):
    rows[i] = rows[i] + [-g.get(m, 0) for g in NFextra]      # SOS side moves to the left with a minus sign
for i in range(len(nondes), len(rows)):
    rows[i] = rows[i] + [Fr(0)] * len(extra)
UNK = list(LHSvars) + [("B",) + key for key in extra]
log("stage-1 system:", len(rows), "x", len(UNK))
# solve rows * x = rhs with x = rounded + dx, dx supported on pivots (prefer LHS unknowns, then smooth pivots)
x_vec = [xL[v] for v in LHSvars] + [Bq[key] for key in extra]
def smooth(q):
    q = abs(Fr(q))
    if q == 0: return False
    for nn in (q.numerator, q.denominator):
        for pr in (2, 3, 5):
            while nn % pr == 0: nn //= pr
        if nn != 1: return False
    return True
res = [rhs[i] - sum(rows[i][j] * x_vec[j] for j in range(len(UNK)) if rows[i][j] != 0) for i in range(len(rows))]
A = [list(r) + [res[i]] for i, r in enumerate(rows)]; ncol = len(UNK)
piv = []; rI = 0
used = set()
for _ in range(len(A)):
    best = None
    for i in range(rI, len(A)):
        for j in range(ncol):
            if j in used or A[i][j] == 0: continue
            sc_ = (0 if j < len(LHSvars) else 1, 0 if smooth(A[i][j]) else 1, -abs(float(A[i][j])))
            if best is None or sc_ < best[0]: best = (sc_, i, j)
    if best is None: break
    _, i, j = best; A[rI], A[i] = A[i], A[rI]
    pv = A[rI][j]; A[rI] = [x / pv for x in A[rI]]
    for ii in range(len(A)):
        if ii != rI and A[ii][j] != 0:
            f = A[ii][j]; A[ii] = [a - f * b for a, b in zip(A[ii], A[rI])]
    piv.append(j); used.add(j); rI += 1
assert all(all(x == 0 for x in A[i]) for i in range(rI, len(A))), "stage 1 inconsistent"
dx = [Fr(0)] * ncol
for i, j in enumerate(piv): dx[j] = A[i][-1]
x_vec = [x_vec[j] + dx[j] for j in range(ncol)]
for i in range(len(rows)):
    assert sum(rows[i][j] * x_vec[j] for j in range(ncol) if rows[i][j] != 0) == rhs[i]
xL = dict(zip(LHSvars, x_vec[:len(LHSvars)]))
for key, v in zip(extra, x_vec[len(LHSvars):]):
    if v != Bq[key]:
        SOSr = padd(SOSr, gens[key], v - Bq[key]); Bq[key] = v
log(f"stage 1: {len(rows)} equations, {len(piv)} pivots; max |dx| = {float(max(abs(v) for v in dx)):.2e};",
    "max denominator bits", max(v.denominator.bit_length() for v in x_vec))

# ---------------------------------------------------------------- stage 2
Lx = dict(L0)
for v, c in zip(LHSvars, LHScols):
    if xL[v] != 0: Lx = padd(Lx, c, xL[v])
rec = {}
rest = NF(padd(Lx, SOSr, -1), rec)
assert not rest, f"stage 2 remainder not zero: {list(rest.items())[:4]}"
for key, dlt in rec.items(): Bq[key] += dlt
log(f"stage 2: {len(rec)} designated entries adjusted, max |delta| = {float(max(abs(v) for v in rec.values())):.2e}")
# full exact re-check of the identity
SOS = {}
for key, G in gens.items():
    if Bq[key] != 0: SOS = padd(SOS, G, Bq[key])
assert padd(Lx, SOS, -1) == {}, "identity check failed"
log("identity exact")

# ---------------------------------------------------------------- PSD data (LDL^T + DD remainder), exact check
def block_mat(kind, blk, size):
    M = [[Fr(0)] * size for _ in range(size)]
    if kind == "F":
        for (kk, a, b), v in xL.items():
            if kk == "F" and a == blk: M[b[0]][b[1]] = M[b[1]][b[0]] = v
    else:
        for (r_, p, q), v in Bq.items():
            if r_ == blk: M[p][q] = M[q][p] = v
    return M
def psd_cert(M):
    m = len(M); Mf = np.array([[float(x) for x in row] for row in M])
    lam = np.linalg.eigvalsh(Mf)[0]; assert lam > 0, lam
    Lc = np.linalg.cholesky(Mf - (lam / 2) * np.eye(m))        # M - eps I = Lc Lc^T
    dd = np.diag(Lc) ** 2; Lu = Lc / np.diag(Lc)                 # unit lower triangular
    l = [[Fr(round(Lu[a, q] * 2 ** 52), 2 ** 52) if a != q else Fr(1) for a in range(m)] for q in range(m)]
    for q in range(m):
        for a in range(q): l[q][a] = Fr(0)
    dq = [Fr(round(x * 2 ** 60), 2 ** 60) for x in dd]
    Delta = [[M[a][c] - sum(dq[q] * l[q][a] * l[q][c] for q in range(m)) for c in range(m)] for a in range(m)]
    ok = all(dq[q] >= 0 for q in range(m)) and all(Delta[a][c] == Delta[c][a] for a in range(m) for c in range(m)) and \
         all(sum(abs(Delta[a][c]) for c in range(m) if c != a) <= Delta[a][a] for a in range(m))
    assert ok, "DD remainder check failed"
    return dict(d=[str(x) for x in dq], l=[[str(x) for x in row] for row in l], min_eig=float(lam))
Fred_out = [[[str(x) for x in row] for row in N] for N, _, _ in Fn]
Sred_out = [[[str(x) for x in row] for row in N] for N, _, _ in Sn]
Fm = [block_mat("F", k, len(Fn[k][0][0])) for k in range(len(Fn))]
Bm = [block_mat("B", r_, len(Sn[r_][0][0])) for r_ in range(len(Sn))]
psdF = [psd_cert(M) for M in Fm]; psdB = [psd_cert(M) for M in Bm]
log("PSD certificates: min eig F'", [f"{c['min_eig']:.1e}" for c in psdF], " B'", [f"{c['min_eig']:.1e}" for c in psdB])
s = lambda v: f"{v.numerator}/{v.denominator}" if v.denominator != 1 else str(v.numerator)
cert = dict(description=("N = 5, Riesz s = 2: SHORT exact three-point certificate (re-rounded from the float SDP; "
                         "same semantics as cert_n5_s2.json). AI-produced, not peer reviewed."),
            D=D, n=n, e="17/4", H_chebyshev=[s(xL[("h", j, None)]) for j in range(D + 1)],
            F_reducers=Fred_out, F_reduced=[[[s(v) for v in row] for row in M] for M in Fm],
            sos_g=["1", "1+u", "1+v", "1+t", "1-u", "1-v", "1-t", "detG=1+2uvt-u^2-v^2-t^2"], sos_degrees=DEG,
            sos_monomials="all (a,b,c) with a+b+c <= d, in itertools.product order",
            sos_reducers=Sred_out, sos_reduced=[[[s(v) for v in row] for row in M] for M in Bm],
            psd=dict(F=psdF, B=psdB), reround=dict(K=K, script="numerics/n5/lean/short_s2.py"))
json.dump(cert, open(OUT, "w"))
allnums = [Fr(x) for x in cert["H_chebyshev"]] + [Fr(v) for M in cert["F_reduced"] + cert["sos_reduced"] for row in M for v in row]
log(f"wrote {OUT}: {len(json.dumps(cert)) // 1024} KB; max bits of any certificate number:",
    max(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) for q in allnums))
