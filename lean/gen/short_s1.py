#!/usr/bin/env python3
"""Short exact re-rounding of the N = 5 Coulomb (Riesz s = 1) three-point certificate over K = Q(sqrt2, sqrt3), for Lean.

Input:  stage_s1.pkl  (reducers, column layout) and stage2_s1.pkl (the exact solution xK of the published certificate,
        K-components), written by construction/1c_build_sdp_coulomb.py and 2c_exact_coulomb.py with RIESZ_S=1
Output: cert_n5_s1_short.json in the format of cert_n5_s1.json (check/check_n5_odd.py verifies it unchanged).

Method: lean/gen/short_s2.py applied per K-component. The constraint matrix is rational and the right-hand side
lies in K, so the system splits into four rational systems A x_c = b_c (c = 1, sqrt2, sqrt3, sqrt6) with the same A,
the same reducers, the same designated generators and the same stage-1 pivots. Per component c:
  * targets: the K-components of the published exact solution (their real combination is the published certificate,
    positive definite with margin ~2e-7); reducers normalised to echelon form (B'_new = S B'_old S);
  * all unknowns rounded to 2^-K; stage 1: LHS unknowns (H, F') and non-designated SOS entries solve the non-designated
    normal-form equations + the five touching pins (component c of the K-valued touching values) by one Gauss-Jordan
    elimination with greedy smooth pivots (pivots depend only on A, so they are shared by the four components);
  * stage 2: the residual is reduced by the designated generators (leading coefficients +-1, +-2) and absorbed into
    the designated reduced Gram entries; the remainder is exactly 0; full exact identity re-check per component.
The b_sqrt6 component is 0 and the published solution has zero sqrt6-component; it stays exactly 0.
Positive definiteness at the corners of a rational box around (sqrt2, sqrt3, sqrt6) is established in corner_s1.py.
usage: python3 short_s1.py [K=40] [out=cert_n5_s1_short.json]
"""
import sys, os, json, pickle, itertools, time
from fractions import Fraction as Fr
import numpy as np

T0 = time.time()
def log(*a): print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "odd", "s1_D10")
K = int(sys.argv[1]) if len(sys.argv) > 1 else 40
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "cert_n5_s1_short.json")
d = pickle.load(open(os.path.join(SRC, "stage_s1.pkl"), "rb"))
xK = pickle.load(open(os.path.join(SRC, "stage2_s1.pkl"), "rb"))["xK"]
cols = d["cols"]
D = 10; n = 5
E_K = (Fr(1, 2), Fr(3), Fr(1), Fr(0))                 # E(TBP) = 1/2 + 3 sqrt2 + sqrt3
PV = (1.0, 2 ** 0.5, 3 ** 0.5, 6 ** 0.5)
NC = 4

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
    return N, free, scale
Fn = [normalise(M) for M in d["Fred"]]; Sn = [normalise(M) for M in d["SRED"]]
def old_block_exact(kind, blk, comp):
    idx = [(ci, p, q) for ci, (kk, bb, p, q) in enumerate(cols) if kk == kind and bb == blk]
    m = max(max(p, q) for _, p, q in idx) + 1; Mx = [[Fr(0)] * m for _ in range(m)]
    for ci, p, q in idx: Mx[p][q] = Mx[q][p] = xK[ci][comp]
    return Mx
def new_block(kind, blk, comp, s):
    Mo = old_block_exact(kind, blk, comp); m = len(Mo)
    return [[s[a] * s[b] * Mo[a][b] for b in range(m)] for a in range(m)]
hcK = [xK[ci] for ci, (kk, bb, p, q) in enumerate(cols) if kk == "h"]
FfK = [[new_block("F", k, c, s) for c in range(NC)] for k, (_, _, s) in enumerate(Fn)]
BfK = [[new_block("B", r, c, s) for c in range(NC)] for r, (_, _, s) in enumerate(Sn)]
def realf(Ms):
    return sum(PV[c] * np.array([[float(x) for x in row] for row in Ms[c]]) for c in range(NC))
log("normalised reducers; min eig of the real blocks F':", [f"{np.linalg.eigvalsh(realf(M))[0]:.2e}" for M in FfK],
    "B':", [f"{np.linalg.eigvalsh(realf(M))[0]:.2e}" for M in BfK])
log("component max |entry|:", [f"{max(abs(float(x)) for M in FfK + BfK for row in M[c] for x in row):.2e}" for c in range(NC)])

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
L0 = [{(0, 0, 0): -E_K[c] / 10} if E_K[c] != 0 else {} for c in range(NC)]
gens = {}
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

# ---------------------------------------------------------------- rounding (exact, from the exact components)
def rnd(x): return Fr(round(Fr(x) * (1 << K)), 1 << K)
xL = [{} for _ in range(NC)]
for c in range(NC):
    for (kind, a, b) in LHSvars:
        xL[c][(kind, a, b)] = rnd(hcK[a][c]) if kind == "h" else rnd(FfK[a][c][b[0]][b[1]])
Bq = [{key: rnd(BfK[key[0]][c][key[1]][key[2]]) for key in gens} for c in range(NC)]
log("rounded to 2^-%d; building stage 1" % K)

# ---------------------------------------------------------------- stage 1 (shared pivots, four right-hand sides)
NFcols = [NF(cc) for cc in LHScols]; NFL0 = [NF(L0[c]) for c in range(NC)]
rows, rhs = [], [[] for _ in range(NC)]
for m in nondes:
    rows.append([cc.get(m, 0) for cc in NFcols])
    for c in range(NC): rhs[c].append(-NFL0[c].get(m, 0))
# touching pins: H(-1) = 1/2, H(-1/2) = sqrt3/3, H(0) = sqrt2/2, H'(-1/2) = sqrt3/9, H'(0) = sqrt2/4  (K-components)
pins = [(-1, 0, (Fr(1, 2), 0, 0, 0)), (Fr(-1, 2), 0, (0, 0, Fr(1, 3), 0)), (0, 0, (0, Fr(1, 2), 0, 0)),
        (Fr(-1, 2), 1, (0, 0, Fr(1, 9), 0)), (0, 1, (0, Fr(1, 4), 0, 0))]
for (t0, der, val), tt in zip(pins, d["TOUCH"]):
    assert float(t0) == tt[0] and der == tt[1] and [Fr(v) for v in val] == [Fr(v) for v in tt[2]]
    row = [Fr(0)] * len(LHSvars)
    for j in range(D + 1):
        cj = cheb(j)
        row[j] = sum(cj[a] * Fr(t0) ** a for a in range(len(cj))) if der == 0 else \
                 sum(a * cj[a] * Fr(t0) ** (a - 1) for a in range(1, len(cj)))
    rows.append(row)
    for c in range(NC): rhs[c].append(Fr(val[c]))
desig_keys = {key for key, _ in desig.values()}
extra = [key for key in gens if key not in desig_keys]
log("computing NF of", len(extra), "non-designated generators")
NFextra = [NF(gens[key]) for key in extra]
for i, m in enumerate(nondes):
    rows[i] = rows[i] + [-g.get(m, 0) for g in NFextra]
for i in range(len(nondes), len(rows)):
    rows[i] = rows[i] + [Fr(0)] * len(extra)
UNK = list(LHSvars) + [("B",) + key for key in extra]
ncol = len(UNK)
log("stage-1 system:", len(rows), "x", ncol, "with", NC, "right-hand sides")
x_vec = [[xL[c][v] for v in LHSvars] + [Bq[c][key] for key in extra] for c in range(NC)]
def smooth(q):
    q = abs(Fr(q))
    if q == 0: return False
    for nn in (q.numerator, q.denominator):
        for pr in (2, 3, 5):
            while nn % pr == 0: nn //= pr
        if nn != 1: return False
    return True
res = [[rhs[c][i] - sum(rows[i][j] * x_vec[c][j] for j in range(ncol) if rows[i][j] != 0) for c in range(NC)]
       for i in range(len(rows))]
A = [list(r) + res[i] for i, r in enumerate(rows)]
piv = []; rI = 0; used = set()
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
log("stage-1 pivots:", [UNK[j] for j in piv])
maxdx = []
for c in range(NC):
    dx = [Fr(0)] * ncol
    for i, j in enumerate(piv): dx[j] = A[i][ncol + c]
    x_vec[c] = [x_vec[c][j] + dx[j] for j in range(ncol)]
    for i in range(len(rows)):
        assert sum(rows[i][j] * x_vec[c][j] for j in range(ncol) if rows[i][j] != 0) == rhs[c][i]
    xL[c] = dict(zip(LHSvars, x_vec[c][:len(LHSvars)]))
    for key, v in zip(extra, x_vec[c][len(LHSvars):]): Bq[c][key] = v
    maxdx.append(float(max(abs(v) for v in dx)))
log(f"stage 1: {len(rows)} equations, {len(piv)} pivots; max |dx| per component:", [f"{v:.2e}" for v in maxdx])

# ---------------------------------------------------------------- stage 2, per component
for c in range(NC):
    Lx = dict(L0[c])
    for v, cc in zip(LHSvars, LHScols):
        if xL[c][v] != 0: Lx = padd(Lx, cc, xL[c][v])
    SOSr = {}
    for key, G in gens.items():
        if Bq[c][key] != 0: SOSr = padd(SOSr, G, Bq[c][key])
    rec = {}
    rest = NF(padd(Lx, SOSr, -1), rec)
    assert not rest, f"stage 2 remainder not zero (component {c})"
    for key, dlt in rec.items(): Bq[c][key] += dlt
    SOS = {}
    for key, G in gens.items():
        if Bq[c][key] != 0: SOS = padd(SOS, G, Bq[c][key])
    assert padd(Lx, SOS, -1) == {}, f"identity check failed (component {c})"
    log(f"stage 2, component {c}: {len(rec)} designated entries adjusted, max |delta| = "
        f"{float(max([abs(v) for v in rec.values()] or [0])):.2e}; identity exact")

# ---------------------------------------------------------------- output
def block_mat(c, kind, blk, size):
    M = [[Fr(0)] * size for _ in range(size)]
    if kind == "F":
        for (kk, a, b), v in xL[c].items():
            if kk == "F" and a == blk: M[b[0]][b[1]] = M[b[1]][b[0]] = v
    else:
        for (r_, p, q), v in Bq[c].items():
            if r_ == blk: M[p][q] = M[q][p] = v
    return M
FmK = [[block_mat(c, "F", k, len(Fn[k][0][0])) for c in range(NC)] for k in range(len(Fn))]
BmK = [[block_mat(c, "B", r_, len(Sn[r_][0][0])) for c in range(NC)] for r_ in range(len(Sn))]
eigF = [np.linalg.eigvalsh(realf(M))[0] for M in FmK]; eigB = [np.linalg.eigvalsh(realf(M))[0] for M in BmK]
log("min eig (float, at p) F':", [f"{x:.2e}" for x in eigF], " B':", [f"{x:.2e}" for x in eigB])
assert min(eigF + eigB) > 0
dev_old = max(float(max(abs(realf(M)[a, b] - realf(Mo)[a, b]) for a in range(len(M[0])) for b in range(len(M[0]))))
              for M, Mo in zip(FmK + BmK, FfK + BfK))
log(f"max |real entry change| vs the published certificate (normalised coordinates): {dev_old:.2e}")
s = lambda v: f"{v.numerator}/{v.denominator}" if v.denominator != 1 else str(v.numerator)
def kmat(Ms): return [[[s(Ms[c][a][b]) for c in range(NC)] for b in range(len(Ms[0]))] for a in range(len(Ms[0]))]
cert = dict(
    description=("N = 5 points on S^2, Coulomb (s = 1, phi(t) = (2-2t)^(-1/2)): SHORT exact three-point certificate over "
                 "K = Q(sqrt2, sqrt3); every number is [a, b, c, d] = a + b sqrt2 + c sqrt3 + d sqrt6. Re-rounded per "
                 "K-component from the published cert_n5_s1.json (same semantics; reducers in echelon form). "
                 "AI-produced, not peer reviewed."),
    D=D, n=n, e=[s(x) for x in E_K], H_chebyshev=[[s(xL[c][("h", j, None)]) for c in range(NC)] for j in range(D + 1)],
    F_reducers=[[[s(x) for x in row] for row in N] for N, _, _ in Fn], F_reduced=[kmat(M) for M in FmK],
    sos_g=["1", "1+u", "1+v", "1+t", "1-u", "1-v", "1-t", "detG=1+2uvt-u^2-v^2-t^2"], sos_degrees=DEG,
    sos_monomials="all (a,b,c) with a+b+c <= d, in itertools.product order",
    sos_reducers=[[[s(x) for x in row] for row in N] for N, _, _ in Sn], sos_reduced=[kmat(M) for M in BmK],
    reround=dict(K=K, script="numerics/n5/lean_s1/short_s1.py", source="numerics/n5/odd/s1_D10/stage2_s1.pkl",
                 min_eig_at_p=dict(F=[float(x) for x in eigF], B=[float(x) for x in eigB])))
json.dump(cert, open(OUT, "w"))
nums = [Fr(x) for z in cert["H_chebyshev"] for x in z] + \
       [Fr(x) for M in cert["F_reduced"] + cert["sos_reduced"] for row in M for z in row for x in z]
redn = [Fr(x) for M in cert["F_reducers"] + cert["sos_reducers"] for row in M for x in row]
bits = lambda L: max(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) for q in L)
log(f"wrote {OUT}: {os.path.getsize(OUT) // 1024} KB; max bits: certificate numbers {bits(nums)}, reducers {bits(redn)}")
log("all certificate denominators 2,3,5-smooth:", all(smooth(Fr(1, q.denominator)) for q in nums))
