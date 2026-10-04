#!/usr/bin/env python3
"""emit_n5.py -- N = 5, Riesz s = 2: exact facially reduced three-point certificate (JSON) -> Lean modules.

usage (run with `nice -n 19`, OMP_NUM_THREADS=1):
  python3 emit_n5.py <cert_n5_s2_short.json> [--outdir DIR]       emit, then run --check on the emitted files
  python3 emit_n5.py --check [--outdir DIR] [--json <cert.json>]  re-read the EMITTED .lean files and re-run, in
                                                                  Python, every Lean Bool check they contain

Output (default DIR = ../N5R2, relative to this script), modules `N5R2.*`:
  Data.lean     `N5R2.cf : ThomsonN7.Cert.Cert3` (n = 5, Λ = lam_, cut an/ad = -1/1, h_ = Λ·H, eps_ = Λ·17/4) whose
                blocks are the EXPANSIONS N·B′·Nᵀ: kernel blocks `F0..F3 = ⟨[], [], F<k>_D⟩` (literal lists), SOS blocks
                `S0..S7` with Gram data `⟨[], [], S<r>_D⟩` (`S<r>_D` packed by `unpackM`); and the facially reduced
                witnesses `nF0..nF3`, `nS0..nS7 : NBlk` (integer basis N, packed reduced block B′ = LDLᵀ + Δ).
  ChkF.lean     Kronecker statistics of the pieces `hE cf.h`, `c1FtotK cf.n (fkE ..)` (k = 0..3); `F<k>_D =
                nF<k>.expandΔ`, `nF<k>.okN`, `Cert3.FOK F<k> nF<k>`                         (one `decide` each)
  ChkS<r>.lean  Kronecker statistics of the piece `sblkE cf.an cf.ad S<r>`                  (one `decide`)
  ChkN<r>.lean  `nS<r>.okN`; `entMat nS<r>.inner = nS<r>_E` and `S<r>_D = N·E·Nᵀ` row by row (one `decide` per row);
                `Cert3.SOK S<r> nS<r>`
  Check.lean    composition of the statistics (`ThomsonN7.Case1.c1Stat_idE`), `chk cf.idE = true`,
                `List.Forall₂ Cert3.FOK cf.F [nF..]`, `List.Forall₂ Cert3.SOK cf.S [nS..]`
  Bound.lean    `Hn` (H in monomial form, exact rationals), `Hn_eq : Hn x = cf.Hf x`, and
                `bound : 17/4 ≤ ∑_{i<j} Hn ⟪x i, x j⟫` from `ThomsonN7.Cert.Cert3.soundN` (ThomsonGen/Cert/Cert3N.lean)

Semantics of the JSON (check/check_n5_even.py of this repository):
  (H(u)+H(v)+H(t))/3 - e/10 - R(u,v,t) = Σ_r g_r z_rᵀ B_r z_r,  R = (n-2)S(u,v,t) + S(u,u,1) + S(v,v,1) + S(t,t,1)
  + S(1,1,1)/(n-1),  S = Σ_k Σ_ab (F_k)_ab Sym(uᵃ vᵇ Q_k),  F_k = N_k F′_k N_kᵀ,  B_r = M_r B′_r M_rᵀ.
Upstream `Cert3.idE` (ThomsonGen/Cert3.lean) is this identity times 6(n-1)·C(n,2)·Λ, with H = h/Λ, e = eps/Λ,
F_k = ent(F_k)/Λ, and SOS block r contributing gE(codes_r)·zᵀ(ent/Λ)z (all multipliers g_r are upstream codes
`codeE` with constant 1).  Integer data: N = Ñ·diag(1/c) with Ñ integer (c_j = lcm of the denominators of column j),
B′ = diag(c)·B̃·diag(c), Λ·B̃ integer; Λ = lcm(all denominators)·2^s, s minimal such that every Λ·B̃ has an exact
integer LDLᵀ + diagonally dominant remainder (`decompose`, adapted from lean/gen_log/emit_tcert.py of alejandrozarco/thomson-n7-log).  The JSON field
"psd" (rational LDLᵀ data of B′) is NOT used: the integer LDLᵀ + Δ data of Λ·B̃ are recomputed and checked.

The Python mirror of the Lean definitions (Ex trees, `Cert3`, `c1Stat`, `unpackI/unpackM`) is that of
lean/gen_log/cert3_util.py of alejandrozarco/thomson-n7-log; the `NBlk` list arithmetic (`padd`, `vecMat`, `matMul`, `matMulT`, `entMat`, `ldl`,
`okF`, `transposeSq`, `domAll`) mirrors ThomsonGen/Cert/NBlk.lean and ThomsonGen/CertF.lean definition by definition.
"""
import argparse, hashlib, itertools, json, os, re, sys, time
from fractions import Fraction as Fr
from math import lcm

sys.setrecursionlimit(1000000)
T0 = time.time()
DEF_OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "N5R2")
NS = "N5R2"


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


# ====================================================================== Kron.Ex mirror (cert3_util.py)
C, MON, ADD, MUL, SB = 0, 1, 2, 3, 4


def c(n): return (C, int(n))
def mon(a, b, d): return (MON, a, b, d)
def add(p, q): return (ADD, p, q)
def mul(p, q): return (MUL, p, q)


U, V, T = mon(1, 0, 0), mon(0, 1, 0), mon(0, 0, 1)
def neg(e): return mul(c(-1), e)
def sub(e, f): return add(e, neg(f))
def smul(a, e): return mul(c(a), e)
def sq(e): return mul(e, e)


def sumE(l):                                  # l.foldr add (c 0)
    r = c(0)
    for x in reversed(l):
        r = add(x, r)
    return r


def sumRange(r, f): return sumE([f(i) for i in range(r)])
def smulNZ(a, e): return c(0) if a == 0 else smul(a, e)


def sbst(i, j, k, e):                         # Cert.sbst, applied lazily at the monomials
    assert e[0] != SB
    return (SB, (i, j, k), e)


def sbst_exps(ijk, a, b, d):
    i, j, k = ijk
    return ((a if i == 0 else 0) + (b if j == 0 else 0) + (d if k == 0 else 0),
            (a if i == 1 else 0) + (b if j == 1 else 0) + (d if k == 1 else 0),
            (a if i == 2 else 0) + (b if j == 2 else 0) + (d if k == 2 else 0))


_q3 = {}


def q3E(k):
    if k not in _q3:
        if k == 0:
            r = c(1)
        elif k == 1:
            r = sub(T, mul(U, V))
        else:
            r = sub(mul(smul(2, sub(T, mul(U, V))), q3E(k - 1)), mul(mul(sub(c(1), sq(U)), sub(c(1), sq(V))), q3E(k - 2)))
        _q3[k] = r
    return _q3[k]


def getD(xs, i, dflt): return xs[i] if i < len(xs) else dflt


class Blk:
    """`structure Blk where d : List ℤ; l : List (List ℤ); Δ : List (List ℤ)` (Cert1.lean)."""
    def __init__(self, d, l, D):
        self.d, self.l, self.D = list(d), [list(x) for x in l], [list(x) for x in D]
    def dq(self, q): return getD(self.d, q, 0)
    def lq(self, q, a): return getD(getD(self.l, q, []), a, 0)
    def dl(self, a, cc): return getD(getD(self.D, a, []), cc, 0)
    def ent(self, r, a, cc): return sum(self.dq(q) * self.lq(q, a) * self.lq(q, cc) for q in range(r)) + self.dl(a, cc)


def fpE(r, b):
    return add(sumRange(r, lambda q: smulNZ(b.dq(q), mul(sumRange(r, lambda a: smulNZ(b.lq(q, a), mon(a, 0, 0))),
                                                         sumRange(r, lambda a: smulNZ(b.lq(q, a), mon(0, a, 0)))))),
               sumRange(r, lambda a: sumRange(r, lambda cc: smulNZ(b.dl(a, cc), mon(a, cc, 0)))))


def fkE(r, b, k): return mul(fpE(r, b), q3E(k))


def sixE(i, j, k, e):
    return add(add(add(add(add(sbst(i, j, k, e), sbst(i, k, j, e)), sbst(j, i, k, e)), sbst(j, k, i, e)),
                   sbst(k, i, j, e)), sbst(k, j, i, e))


def c1FtotK(n, e):
    return add(add(smul((n - 1) * (n - 2), sixE(0, 1, 2, e)),
                   smul(n - 1, add(add(sixE(0, 0, 3, e), sixE(1, 1, 3, e)), sixE(2, 2, 3, e)))),
               sixE(3, 3, 3, e))


def codeE(an, ad, code):
    tbl = {0: lambda: sub(c(1), sq(U)), 1: lambda: sub(c(1), sq(V)), 2: lambda: sub(c(1), sq(T)),
           3: lambda: sub(add(c(1), smul(2, mul(U, mul(V, T)))), add(sq(U), add(sq(V), sq(T)))),
           4: lambda: sub(c(1), U), 5: lambda: add(c(1), U), 6: lambda: sub(c(1), V), 7: lambda: add(c(1), V),
           8: lambda: sub(c(1), T), 9: lambda: add(c(1), T), 10: lambda: sub(smul(ad, U), c(an)),
           11: lambda: sub(smul(ad, V), c(an)), 12: lambda: sub(smul(ad, T), c(an))}
    return tbl[code]() if code in tbl else c(1)


def gE(an, ad, g):
    r = c(1)
    for code in reversed(g):
        r = mul(codeE(an, ad, code), r)
    return r


def zt(zs, a): return getD(zs, a, (0, 0, 0))
def zmon(zs, a): t = zt(zs, a); return mon(t[0], t[1], t[2])


def zzmon(zs, a, cc):
    s, t = zt(zs, a), zt(zs, cc)
    return mon(s[0] + t[0], s[1] + t[1], s[2] + t[2])


def sqfE(b, zs):
    L = len(zs)
    return add(sumRange(L, lambda q: smulNZ(b.dq(q), sq(sumRange(L, lambda a: smulNZ(b.lq(q, a), zmon(zs, a)))))),
               sumRange(L, lambda a: sumRange(L, lambda cc: smulNZ(b.dl(a, cc), zzmon(zs, a, cc)))))


def perm3(s): return {0: (0, 1, 2), 1: (0, 2, 1), 2: (1, 0, 2), 3: (1, 2, 0), 4: (2, 0, 1)}.get(s, (2, 1, 0))


class SBlk:
    def __init__(self, g, sigma, z, B):
        self.g, self.sigma, self.z, self.B = list(g), sigma, [tuple(x) for x in z], B


def sblkE(an, ad, s):
    p = perm3(s.sigma)
    return sbst(p[0], p[1], p[2], mul(gE(an, ad, s.g), sqfE(s.B, s.z)))


def hE(h):
    return sumRange(len(h), lambda j: smulNZ(getD(h, j, 0), add(add(mon(j, 0, 0), mon(0, j, 0)), mon(0, 0, j))))


class Cert3:
    def __init__(self, n, Lam, an, ad, h, eps, F, S):
        self.n, self.Lam, self.an, self.ad, self.h, self.eps, self.F, self.S = n, Lam, an, ad, list(h), eps, F, S
    def blk(self, k): return getD(self.F, k, Blk([], [], []))
    def m(self, k): return len(self.blk(k).D)
    @property
    def K(self): return len(self.F)


# ---- Case1Stat.lean: c1Stat and the composition c1Stat_idE
def c1Add(s, t): return (s[0] + t[0], max(s[1], t[1]), max(s[2], t[2]), max(s[3], t[3]), s[4] + t[4])
def c1Mul(s, t): return (s[0] * t[0], s[1] + t[1], s[2] + t[2], s[3] + t[3], s[4] * t[4])
def c1C(a): return (abs(a), 0, 0, 0, a)
def c1Sub(s, t): return c1Add(s, c1Mul(c1C(-1), t))
def c1Smul(a, s): return c1Mul(c1C(a), s)


def c1Sum(l):
    r = c1C(0)
    for x in reversed(l):
        r = c1Add(x, r)
    return r


def stat_l(e):
    """(Ex.l1, Ex.dx, Ex.dy, Ex.dz) by structural recursion (sbst applied at the monomials)."""
    memo = {}

    def go(e, ijk):
        key = (id(e), ijk)
        if key in memo:
            return memo[key][0]
        tg = e[0]
        if tg == C:
            r = (abs(e[1]), 0, 0, 0)
        elif tg == MON:
            a, b, d = e[1], e[2], e[3]
            if ijk is not None:
                a, b, d = sbst_exps(ijk, a, b, d)
            r = (1, a, b, d)
        elif tg == SB:
            r = go(e[2], e[1])
        else:
            p, q = go(e[1], ijk), go(e[2], ijk)
            r = (p[0] + q[0], max(p[1], q[1]), max(p[2], q[2]), max(p[3], q[3])) if tg == ADD else \
                (p[0] * q[0], p[1] + q[1], p[2] + q[2], p[3] + q[3])
        memo[key] = (r, e)
        return r
    return go(e, None)


def kev(e, w, D):
    """Ex.kev w D: the integer value at u = 2^w, v = 2^(wD), t = 2^(wD^2)."""
    memo, pw = {}, {}

    def go(e, ijk):
        key = (id(e), ijk)
        if key in memo:
            return memo[key][0]
        tg = e[0]
        if tg == C:
            r = e[1]
        elif tg == MON:
            a, b, d = e[1], e[2], e[3]
            if ijk is not None:
                a, b, d = sbst_exps(ijk, a, b, d)
            code = a + D * b + D * D * d
            r = pw.get(code)
            if r is None:
                r = pw[code] = 1 << (w * code)
        elif tg == SB:
            r = go(e[2], e[1])
        else:
            p, q = go(e[1], ijk), go(e[2], ijk)
            r = p + q if tg == ADD else p * q
        memo[key] = (r, e)
        return r
    return go(e, None)


def nat_log2(n): return n.bit_length() - 1 if n > 0 else 0
def choose2(n): return n * (n - 1) // 2


def pieces(cf):
    out = [("H", hE(cf.h))]
    for k in range(cf.K):
        out.append((f"F{k}", c1FtotK(cf.n, fkE(cf.m(k), cf.blk(k), k))))
    for i, s in enumerate(cf.S):
        out.append((f"S{i}", sblkE(cf.an, cf.ad, s)))
    return out


def compose_idE(cf, stH, stF, stS):
    n, C2 = cf.n, choose2(cf.n)
    return c1Sub(c1Sub(c1Sub(c1Smul(2 * (n - 1) * C2, stH), c1C(6 * (n - 1) * cf.eps)), c1Smul(C2, c1Sum(stF))),
                 c1Smul(6 * (n - 1) * C2, c1Sum(stS)))


def chk_params(l1, dx, dy, dz): return nat_log2(l1) + 1, max(dx, max(dy, dz)) + 1


# ====================================================================== packing (CertF.lean, NBlk.lean)
def unpackI(B, n, x):
    out = []
    for _ in range(n):
        out.append((x % (1 << B)) - (1 << (B - 1)))      # B >= 1 always (width >= 1)
        x >>= B
    return out


def unpackM(B, cols, rows, x):
    out = []
    for _ in range(rows):
        out.append(unpackI(B, cols, x % (1 << (B * cols))))
        x >>= B * cols
    return out


def mkBlk(r, Bd, Bl, BD, xd, xl, xD): return Blk(unpackI(Bd, r, xd), unpackM(Bl, r, r, xl), unpackM(BD, r, r, xD))


def packI(B, vals):
    x, off = 0, 1 << (B - 1)
    for i, v in enumerate(vals):
        f = v + off
        assert 0 <= f < (1 << B), (B, v)
        x |= f << (B * i)
    return x


def packM(B, cols, rows):
    x = 0
    for i, row in enumerate(rows):
        assert len(row) == cols
        x |= packI(B, row) << (B * cols * i)
    return x


def width(vals):
    """least B >= 1 with -2^(B-1) <= v < 2^(B-1) for all v."""
    B = 1
    for v in vals:
        while not (-(1 << (B - 1)) <= v < (1 << (B - 1))):
            B += 1
    return B


# ---- NBlk.lean list arithmetic (structural recursion; zip-truncating where Lean truncates)
def padd(p, q):
    out = [a + b for a, b in zip(p, q)]
    return out + (p[len(q):] if len(p) > len(q) else q[len(p):])


def pscale(cst, p): return [cst * x for x in p]
def dot(x, y): return sum(a * b for a, b in zip(x, y))


def vecMat(x, M):
    acc = []
    for a, row in reversed(list(zip(x, M))):
        acc = padd(pscale(a, row), acc)
    return acc


def matMul(A, B): return [vecMat(row, B) for row in A]
def matMulT(A, B): return [[dot(ra, rb) for rb in B] for ra in A]


def matAdd(A, B):
    out = [padd(a, b) for a, b in zip(A, B)]
    return out + (A[len(B):] if len(A) > len(B) else B[len(A):])


def outer(x, y): return [pscale(a, y) for a in x]


def ldl(d, l):
    acc = []
    for dq, lq in reversed(list(zip(d, l))):
        acc = matAdd(outer(pscale(dq, lq), lq), acc)
    return acc


def entMat(b): return matAdd(ldl(b.d, b.l), b.D)


def transposeSq(n, M):
    out = []
    for _ in range(n):
        out.append([row[0] if row else 0 for row in M])
        M = [row[1:] for row in M]
    return out


def offAbs(i, k, row):
    s = 0
    for x in row:
        s += 0 if i == k else abs(x)
        k += 1
    return s


def domAll(k, rows):
    for row in rows:
        if not (offAbs(k, 0, row) <= getD(row, k, 0)):
            return False
        k += 1
    return True


def okF(r, b):
    return all(0 <= x for x in b.d) and [row[:r] for row in b.D] == transposeSq(r, b.D) and domAll(0, b.D)


class NBlk:
    """`structure NBlk where N : List (List ℤ); r Bd Bl BD xd xl xD : ℕ` (NBlk.lean)."""
    def __init__(self, N, r, Bd, Bl, BD, xd, xl, xD):
        self.N, self.r, self.Bd, self.Bl, self.BD, self.xd, self.xl, self.xD = N, r, Bd, Bl, BD, xd, xl, xD
    def inner(self): return mkBlk(self.r, self.Bd, self.Bl, self.BD, self.xd, self.xl, self.xD)
    def okN(self): return okF(self.r, self.inner()) and all(len(row) <= self.r for row in self.N)
    def expandD(self): return matMulT(matMul(self.N, entMat(self.inner())), self.N)
    def X_of(self, E): return [[dot(vecMat(row, E), rb) for rb in self.N] for row in self.N]


# ====================================================================== exact integer LDLᵀ + DD remainder
# (decompose / pivot_order / verify_decomp: adapted from lean/gen_log/emit_tcert.py of alejandrozarco/thomson-n7-log)
def round_div(a, b):
    return (2 * a + b) // (2 * b)


def decompose(M, order=None):
    n = len(M)
    if order is None:
        order = list(range(n))
    A = [[M[order[i]][order[j]] for j in range(n)] for i in range(n)]
    d = [0] * n
    L = [[0] * n for _ in range(n)]
    for q in range(n):
        p = A[q][q]
        rowq = A[q]
        left = sum(abs(rowq[cc]) for cc in range(q))
        if p < left:
            return None
        rest = range(q + 1, n)
        best = None
        s0 = max(0, (max(1, n - q) * max(p, 1)).bit_length() // 3)
        for s in range(max(0, s0 - 4), s0 + 5):
            margin = left
            for _ in range(12):
                dq = (p - margin) >> (2 * s) if p > margin else 0
                if dq <= 0:
                    dq = 0
                    lv = [0] * n
                    right = sum(abs(rowq[cc]) for cc in rest)
                else:
                    sc = dq << s
                    lv = [0] * n
                    right = 0
                    for cc in rest:
                        x = round_div(rowq[cc], sc)
                        lv[cc] = x
                        right += abs(rowq[cc] - sc * x)
                diag = p - (dq << (2 * s))
                if diag >= left + right:
                    cand = (diag, s, dq, lv)
                    if best is None or cand[0] < best[0]:
                        best = cand
                    break
                if dq == 0:
                    break
                margin = left + right + (right >> 8) + 1
        if best is None:
            return None
        diag, s, dq, lv = best
        if dq > 0:
            lv[q] = 1 << s
        L[q] = lv
        d[q] = dq
        if dq:
            v = lv
            for a in range(q, n):
                if v[a] == 0:
                    continue
                da = dq * v[a]
                Aa = A[a]
                for cc in range(q, n):
                    if v[cc]:
                        Aa[cc] -= da * v[cc]
    return order, d, L, A


def verify_decomp(M, order, d, L, Delta):
    n = len(M)
    return all(sum(d[q] * L[q][a] * L[q][cc] for q in range(n) if d[q] and L[q][a] and L[q][cc]) + Delta[a][cc]
               == M[order[a]][order[cc]] for a in range(n) for cc in range(n))


def pivot_order(M):
    import numpy as np
    sh = max(0, max(abs(x) for row in M for x in row).bit_length() - 900)
    A = np.array([[float(x >> sh) for x in row] for row in M])
    A = A / max(1.0, float(np.max(np.abs(A))))
    n = len(A)
    idx = list(range(n))
    order = []
    for _ in range(n):
        j = max(idx, key=lambda i: A[i, i])
        order.append(j)
        idx.remove(j)
        pj = A[j, j]
        if pj <= 0:
            order.extend(idx)
            break
        col = A[:, j].copy()
        for i in idx:
            A[i, idx] -= col[i] * col[idx] / pj
    return order


def packed_bits(d, L, Dl):
    return width(d), width([x for row in L for x in row]), width([x for row in Dl for x in row])


# ====================================================================== JSON -> integer certificate
GCODES = {"1": [], "1+u": [5], "1+v": [7], "1+t": [9], "1-u": [4], "1-v": [6], "1-t": [8],
          "detG=1+2uvt-u^2-v^2-t^2": [3]}


def monos_upto(d): return [m for m in itertools.product(range(d + 1), repeat=3) if sum(m) <= d]


def cheb_mono(j):
    a, b = [Fr(1)], [Fr(0), Fr(1)]
    if j == 0:
        return a
    for _ in range(j - 1):
        nb = [Fr(0)] + [2 * x for x in b]
        for i, x in enumerate(a):
            nb[i] -= x
        a, b = b, nb
    return b


def H_monomial(J):
    Hc = [Fr(x) for x in J["H_chebyshev"]]
    out = [Fr(0)] * len(Hc)
    for j, cj in enumerate(Hc):
        for i, x in enumerate(cheb_mono(j)):
            out[i] += cj * x
    return out


def poly_expand(e):
    """collected polynomial {(a,b,d): int} of an Ex tree without SB nodes."""
    tg = e[0]
    if tg == C:
        return {(0, 0, 0): e[1]} if e[1] else {}
    if tg == MON:
        return {(e[1], e[2], e[3]): 1}
    p, q = poly_expand(e[1]), poly_expand(e[2])
    r = {}
    if tg == ADD:
        for k, v in list(p.items()) + list(q.items()):
            r[k] = r.get(k, 0) + v
    else:
        for k1, v1 in p.items():
            for k2, v2 in q.items():
                k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
                r[k] = r.get(k, 0) + v1 * v2
    return {k: v for k, v in r.items() if v}


def int_cols(N):
    """N (rational, m x r) = Ñ diag(1/c): Ñ integer, c_j = lcm of the denominators of column j."""
    k = len(N[0]) if N and N[0] else 0
    cs = []
    for j in range(k):
        L = 1
        for row in N:
            L = lcm(L, row[j].denominator)
        cs.append(L)
    return [[int(row[j] * cs[j]) for j in range(k)] for row in N], cs


def build(J):
    assert J["n"] == 5 and J["D"] == 10 and Fr(J["e"]) == Fr(17, 4)
    n, e = 5, Fr(17, 4)
    Hm = H_monomial(J)
    blocks = []                                    # (kind, index, m, Ni, R)
    for k, (N, Fp) in enumerate(zip(J["F_reducers"], J["F_reduced"])):
        Nq = [[Fr(x) for x in row] for row in N]
        assert len(Nq) == J["D"] // 2 + 1 - k
        Ni, cs = int_cols(Nq)
        R = [[Fr(x) / (cs[i] * cs[j]) for j, x in enumerate(row)] for i, row in enumerate(Fp)]
        blocks.append(("F", k, len(Nq), Ni, R))
    assert J["sos_degrees"] == [5, 4, 4, 4, 4, 4, 4, 3] and len(J["sos_g"]) == 8
    for r_, (g, d, M, Bp) in enumerate(zip(J["sos_g"], J["sos_degrees"], J["sos_reducers"], J["sos_reduced"])):
        Mq = [[Fr(x) for x in row] for row in M]
        assert len(Mq) == len(monos_upto(d))
        Ni, cs = int_cols(Mq)
        R = [[Fr(x) / (cs[i] * cs[j]) for j, x in enumerate(row)] for i, row in enumerate(Bp)]
        blocks.append(("S", r_, len(Mq), Ni, R))
    L0 = 1
    for x in Hm + [e]:
        L0 = lcm(L0, x.denominator)
    for (_, _, _, _, R) in blocks:
        for row in R:
            for x in row:
                L0 = lcm(L0, x.denominator)
    log(f"Λ0 = lcm of denominators: {L0.bit_length()} bits")
    for s in range(0, 64):
        Lam = L0 << s
        res, ok = [], True
        for (kind, idx, m, Ni, R) in blocks:
            Mi = [[int(x * Lam) for x in row] for row in R]
            assert all(Fr(Mi[i][j]) == R[i][j] * Lam for i in range(len(R)) for j in range(len(R)))
            best = None
            for order in ([None, pivot_order(Mi)] if len(Mi) > 1 else [None]):
                out = decompose(Mi, order)
                if out is None:
                    continue
                o, d, L, Dl = out
                bits = sum(packed_bits(d, L, Dl))
                if best is None or bits < best[0]:
                    best = (bits, out)
            if best is None:
                ok = False
                log(f"  s = {s}: no LDLᵀ + DD decomposition for {kind}{idx}")
                break
            o, d, L, Dl = best[1]
            r = len(d)
            assert verify_decomp(Mi, o, d, L, Dl)
            Np = [[row[o[i]] for i in range(r)] for row in Ni]
            res.append((kind, idx, m, Np, d, L, Dl))
        if ok:
            break
    else:
        raise SystemExit("no Λ found")
    log(f"Λ = Λ0·2^{s}: {Lam.bit_length()} bits")
    h = [Hm[i] * Lam for i in range(len(Hm))]
    assert all(x.denominator == 1 for x in h) and (e * Lam).denominator == 1
    data = dict(n=n, Lam=Lam, an=-1, ad=1, h=[int(x) for x in h], eps=int(e * Lam), s=s, L0=L0, NF=[], NSB=[],
                codes=[], z=[])
    for (kind, idx, m, Np, d, L, Dl) in res:
        r = len(d)
        Bd, Bl, BD = packed_bits(d, L, Dl)
        nb = NBlk(Np, r, Bd, Bl, BD, packI(Bd, d), packM(Bl, r, L), packM(BD, r, Dl))
        if kind == "F":
            data["NF"].append(nb)
        else:
            data["NSB"].append(nb)
            data["codes"].append(GCODES[J["sos_g"][idx]])
            data["z"].append(monos_upto(J["sos_degrees"][idx]))
    return data


def cert_of(data, FD=None, SD=None):
    """the expanded `Cert3` (Python mirror); FD/SD: stored expanded remainders (default: recomputed)."""
    FD = FD if FD is not None else [nb.expandD() for nb in data["NF"]]
    SD = SD if SD is not None else [nb.expandD() for nb in data["NSB"]]
    F = [Blk([], [], X) for X in FD]
    S = [SBlk(cd, 0, z, Blk([], [], X)) for cd, z, X in zip(data["codes"], data["z"], SD)]
    return Cert3(data["n"], data["Lam"], data["an"], data["ad"], data["h"], data["eps"], F, S)


# ====================================================================== simulation of every Lean Bool check
def simulate(data, FD, SD, SE):
    """FD, SD: the stored expanded remainders (F literal, S packed); SE: the stored entMat of the S blocks."""
    rep, ok = {}, True
    cf = cert_of(data, FD, SD)
    rep["n_ge_3"] = 3 <= cf.n
    rep["Lam_pos"] = 0 < cf.Lam
    rep["ad_pos"] = 0 < cf.ad
    rep["cut"] = Fr(cf.an, cf.ad) <= -1
    ok &= rep["n_ge_3"] and rep["Lam_pos"] and rep["ad_pos"] and rep["cut"]
    # FOK: F<k>_D = nF<k>.expandΔ (one decide), nF<k>.okN
    rep["FOK"] = [(nb.okN(), FD[k] == nb.expandD()) for k, nb in enumerate(data["NF"])]
    ok &= all(a and b for a, b in rep["FOK"])
    # SOK: nS.okN, entMat rows = E rows, lengths, S_D rows = X rows, z.length <= N.length
    rep["SOK"] = []
    for r_, nb in enumerate(data["NSB"]):
        Ein = entMat(nb.inner())
        X = nb.X_of(SE[r_])
        m = len(data["z"][r_])
        parts = dict(okN=nb.okN(), El=len(Ein) == nb.r, Er=len(SE[r_]) == nb.r, Dl=len(SD[r_]) == m, Xr=len(X) == m,
                     Erows=all(getD(Ein, i, []) == getD(SE[r_], i, []) for i in range(nb.r)),
                     Drows=all(getD(SD[r_], a, []) == getD(X, a, []) for a in range(m)),
                     z_le=m <= len(nb.N), X_is_expand=X == nb.expandD())
        rep["SOK"].append(parts)
        ok &= all(parts.values())
    # Kronecker statistics of the pieces, composition, chk
    pcs = pieces(cf)
    lst = {nm: stat_l(e) for nm, e in pcs}
    z0 = lambda nm: lst[nm] + (0,)
    tot0 = compose_idE(cf, z0("H"), [z0(f"F{k}") for k in range(cf.K)], [z0(f"S{i}") for i in range(len(cf.S))])
    w, D = chk_params(*tot0[:4])
    st = {nm: lst[nm] + (kev(e, w, D),) for nm, e in pcs}
    tot = compose_idE(cf, st["H"], [st[f"F{k}"] for k in range(cf.K)], [st[f"S{i}"] for i in range(len(cf.S))])
    rep.update(w=w, D=D, stats=st, total=tot)
    rep["chk"] = tot[4] == 0 and chk_params(*tot[:4]) == (w, D)
    ok &= rep["chk"]
    rep["ok"] = ok
    return rep


def json_crosscheck(data, FD, SD, J):
    """the expanded integer data / Λ equal the JSON rationals exactly (H, e, N F′ Nᵀ, M B′ Mᵀ, multipliers)."""
    Lam = data["Lam"]
    out = {}
    out["H"] = [Fr(x, Lam) for x in data["h"]] == H_monomial(J)
    out["e"] = Fr(data["eps"], Lam) == Fr(J["e"])
    out["cut"] = (data["an"], data["ad"]) == (-1, 1)

    def NFNt(N, Fp):
        Nm = [[Fr(x) for x in row] for row in N]
        Fm = [[Fr(x) for x in row] for row in Fp]
        m, r = len(Nm), len(Fm)
        NF = [[sum((Nm[i][k] * Fm[k][j] for k in range(r)), Fr(0)) for j in range(r)] for i in range(m)]
        return [[sum((NF[i][k] * Nm[j][k] for k in range(r)), Fr(0)) for j in range(m)] for i in range(m)]
    out["F"] = all([[Fr(x, Lam) for x in row] for row in FD[k]] == NFNt(N, Fp)
                   for k, (N, Fp) in enumerate(zip(J["F_reducers"], J["F_reduced"])))
    out["S"] = all([[Fr(x, Lam) for x in row] for row in SD[r_]] == NFNt(M, Bp)
                   for r_, (M, Bp) in enumerate(zip(J["sos_reducers"], J["sos_reduced"])))
    gpoly = {"1": {(0, 0, 0): 1}, "1+u": {(0, 0, 0): 1, (1, 0, 0): 1}, "1+v": {(0, 0, 0): 1, (0, 1, 0): 1},
             "1+t": {(0, 0, 0): 1, (0, 0, 1): 1}, "1-u": {(0, 0, 0): 1, (1, 0, 0): -1},
             "1-v": {(0, 0, 0): 1, (0, 1, 0): -1}, "1-t": {(0, 0, 0): 1, (0, 0, 1): -1},
             "detG=1+2uvt-u^2-v^2-t^2": {(0, 0, 0): 1, (1, 1, 1): 2, (2, 0, 0): -1, (0, 2, 0): -1, (0, 0, 2): -1}}
    out["g"] = all(poly_expand(gE(data["an"], data["ad"], cd)) == gpoly[g] for cd, g in zip(data["codes"], J["sos_g"]))
    out["z"] = all(z == monos_upto(d) for z, d in zip(data["z"], J["sos_degrees"]))
    out["sizes"] = (len(FD) == 4 and len(SD) == 8 and len(data["NF"]) == 4 and len(data["NSB"]) == 8)
    return out


# ====================================================================== Lean emission
def hexs(x): return f"0x{x:x}"


def lint(v): return f"({v} : Int)" if v >= 0 else f"({v} : Int)"


def llist(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
def lmat(M): return "[" + ", ".join(llist(row) for row in M) + "]"


def stat_def(st):
    kv = st[4]
    kvs = f"(0x{kv:x} : Int)" if kv >= 0 else f"(-0x{-kv:x} : Int)"
    return f"({st[0]}, {st[1]}, {st[2]}, {st[3]}, {kvs})"


def header(imports, what, src, sha):
    return ("".join(f"import {i}\n" for i in imports)
            + f"/-! {what}\n\nGenerated by `lean/gen/emit_n5.py` from `{src}`\n(sha256 {sha}).  "
            "Do not edit; regenerate. -/\n\n")


OPEN = ("open ThomsonN7 ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert ThomsonN7.Cert.Cert3\n\n"
        "-- large literals: elaboration budget only (no effect on what is checked)\nset_option maxHeartbeats 0\n\n")


def nblk_lit(nb):
    return (f"⟨{lmat(nb.N)}, {nb.r}, {nb.Bd}, {nb.Bl}, {nb.BD},\n  {hexs(nb.xd)},\n  {hexs(nb.xl)},\n  {hexs(nb.xD)}⟩")


def match_rows(n, name):
    cases = "".join(f"\n      | {i}, _ => {name}{i}" for i in range(n))
    return f"match a, ha with{cases}\n      | _ + {n}, h => absurd h (by omega)"


def emit(data, rep, src, sha, outdir, FD, SD, SDw, SE, SEw):
    os.makedirs(outdir, exist_ok=True)
    files = {}
    w, D = rep["w"], rep["D"]
    K, nS = len(data["NF"]), len(data["NSB"])
    hd = lambda imports, what: header(imports, what, src, sha)
    ns = lambda body: f"namespace {NS}\n" + OPEN + body + f"\nend {NS}\n"
    # ---------------- Data.lean
    L = []
    L.append(f"/-- `Λ · H` in the monomial basis (`H x = ∑_j h_j x^j / Λ`). -/\ndef h_ : List Int := {llist(data['h'])}")
    L.append(f"/-- The common denominator `Λ = Λ0 · 2^{data['s']}`. -/\ndef lam_ : Nat := {data['Lam']}")
    L.append(f"/-- `Λ · e`, `e = 17/4`. -/\ndef eps_ : Int := {lint(data['eps'])}")
    for k, nb in enumerate(data["NF"]):
        L.append(f"/-- Facially reduced kernel block `k = {k}`: `F_{k} = N · B′ · Nᵀ / Λ` ({len(nb.N)} × {nb.r}). -/\n"
                 f"def nF{k} : NBlk :=\n  {nblk_lit(nb)}")
        L.append(f"/-- The expanded remainder `N · B′ · Nᵀ` of `nF{k}`. -/\ndef F{k}_D : List (List Int) := {lmat(FD[k])}")
        L.append(f"def F{k} : Blk := ⟨[], [], F{k}_D⟩")
    for r_, nb in enumerate(data["NSB"]):
        m = len(data["z"][r_])
        zs = "[" + ", ".join(f"({a}, {b}, {cc})" for a, b, cc in data["z"][r_]) + "]"
        L.append(f"/-- Facially reduced SOS block `r = {r_}` ({m} × {nb.r}). -/\ndef nS{r_} : NBlk :=\n  {nblk_lit(nb)}")
        L.append(f"/-- The expanded Gram remainder `N · B′ · Nᵀ` of `nS{r_}` ({m} × {m}, {SDw[r_]}-bit fields). -/\n"
                 f"def S{r_}_D : List (List Int) := unpackM {SDw[r_]} {m} {m}\n  {hexs(packM(SDw[r_], m, SD[r_]))}")
        L.append(f"def S{r_}_z : List (Nat × Nat × Nat) := {zs}")
        L.append(f"def S{r_}_B : Blk := ⟨[], [], S{r_}_D⟩")
        L.append(f"def S{r_} : SBlk := ⟨{llist(data['codes'][r_])}, 0, S{r_}_z, S{r_}_B⟩")
    L.append("/-- The certificate: `n = 5`, no cut (`an / ad = -1`), expanded blocks. -/")
    L.append("def cf : Cert3 :=\n  { n := 5, Lam := lam_, an := -1, ad := 1, h := h_, eps := eps_,\n"
             f"    F := {llist(f'F{k}' for k in range(K))},\n    S := {llist(f'S{r_}' for r_ in range(nS))} }}")
    files["Data.lean"] = hd(["ThomsonGen.Cert.Cert3N"],
                            "N = 5, Riesz s = 2: the exact three-point certificate (degree 10) in upstream's `Cert3` "
                            "format,\nwith facially reduced witnesses.\n\n"
                            "* `cf.Hf x = (∑_{j<11} h_j x^j) / lam_` is the minorant `H`; `eps_ / lam_ = 17/4`;\n"
                            "* `F0..F3`, `S0..S7`: the EXPANDED blocks `⟨[], [], N·B′·Nᵀ⟩` (no pivots; the expanded "
                            "blocks are singular);\n"
                            "* `nF0..nF3`, `nS0..nS7`: the witnesses (`NBlk`: integer basis `N`, reduced block `B′` "
                            "packed by `mkBlk`).\n"
                            "Multiplier codes (`Cert.codeE`): `[]` = 1, `5` = 1+u, `7` = 1+v, `9` = 1+t, `4` = 1-u, "
                            "`6` = 1-v, `8` = 1-t, `3` = Gram determinant.") \
        + ns("\n\n".join(L) + "\n")
    # ---------------- ChkF.lean: statistics of H, F pieces; F block facts
    st = rep["stats"]
    stmt = {"H": f"ThomsonN7.Case1.c1Stat {w} {D} (hE cf.h)"}
    for k in range(K):
        stmt[f"F{k}"] = f"ThomsonN7.Case1.c1Stat {w} {D} (ThomsonN7.Case1.c1FtotK cf.n (fkE (cf.m {k}) (cf.blk {k}) {k}))"
    for r_ in range(nS):
        stmt[f"S{r_}"] = f"ThomsonN7.Case1.c1Stat {w} {D} (sblkE cf.an cf.ad S{r_})"

    def stat_block(nm):
        return (f"/-- Kronecker statistics `(ℓ¹, deg u, deg v, deg t, value)` of the piece `{nm}`. -/\n"
                f"def stat{nm} : ThomsonN7.Case1.C1Stat :=\n  {stat_def(st[nm])}\n\n"
                f"theorem stat_{nm} :\n    {stmt[nm]} = stat{nm} := by\n  decide +kernel\n")
    body = "\n".join(stat_block(nm) for nm in ["H"] + [f"F{k}" for k in range(K)]) + "\n"
    for k in range(K):
        body += (f"theorem F{k}_D_eq : F{k}_D = nF{k}.expandΔ := by decide +kernel\n"
                 f"theorem nF{k}_ok : nF{k}.okN = true := by decide +kernel\n"
                 f"theorem F{k}_fok : Cert3.FOK F{k} nF{k} := Cert3.FOK.intro F{k}_D_eq nF{k}_ok\n\n")
    files["ChkF.lean"] = hd(["ThomsonGen.Case1Stat", f"{NS}.Data"],
                            f"N = 5, s = 2: Kronecker statistics of the pieces `H`, `F0..F{K-1}` (`w = {w}`, "
                            f"`D = {D}`), and the\nkernel blocks as expansions of checked `NBlk`s.  One `decide +kernel` "
                            "per declaration.") + ns(body)
    # ---------------- ChkS<r>.lean
    for r_ in range(nS):
        files[f"ChkS{r_}.lean"] = hd(["ThomsonGen.Case1Stat", f"{NS}.Data"],
                                     f"N = 5, s = 2: Kronecker statistics of the SOS piece `S{r_}` (`w = {w}`, "
                                     f"`D = {D}`).") + ns(stat_block(f"S{r_}"))
    # ---------------- ChkN<r>.lean
    for r_, nb in enumerate(data["NSB"]):
        x = f"nS{r_}"
        m, r = len(data["z"][r_]), nb.r
        B = [f"/-- `entMat` of the reduced block of `{x}` ({r} × {r}, {SEw[r_]}-bit fields). -/\n"
             f"def {x}_E : List (List ℤ) := unpackM {SEw[r_]} {r} {r}\n  {hexs(packM(SEw[r_], r, SE[r_]))}\n\n"
             f"/-- `N · E · Nᵀ` by rows. -/\n"
             f"def {x}_X : List (List ℤ) :=\n  {x}.N.map (fun row => {x}.N.map fun rb => NBlk.dot (NBlk.vecMat row {x}_E) rb)\n\n"
             f"theorem {x}_ok : {x}.okN = true := by decide +kernel\n"
             f"theorem {x}_El : (NBlk.entMat {x}.inner).length = {r} := by decide +kernel\n"
             f"theorem {x}_Er : {x}_E.length = {r} := by decide +kernel\n"
             f"theorem {x}_Dl : S{r_}_D.length = {m} := by decide +kernel\n"
             f"theorem {x}_Xr : {x}_X.length = {m} := by decide +kernel\n"
             f"theorem {x}_z : S{r_}_z.length ≤ {x}.N.length := by decide +kernel\n\n"]
        for i in range(r):
            B.append(f"theorem {x}_E{i} : (NBlk.entMat {x}.inner).getD {i} [] = {x}_E.getD {i} [] := by decide +kernel\n")
        B.append("\n")
        for a in range(m):
            B.append(f"theorem {x}_D{a} : S{r_}_D.getD {a} [] = {x}_X.getD {a} [] := by decide +kernel\n")
        B.append(f"\ntheorem {x}_hE : NBlk.entMat {x}.inner = {x}_E :=\n"
                 f"  NBlk.eq_of_getD_rows ({x}_El.trans {x}_Er.symm) fun a ha => by\n"
                 f"    rw [{x}_El] at ha\n    exact {match_rows(r, x + '_E')}\n\n"
                 f"theorem {x}_hD : S{r_}_D = {x}_X :=\n"
                 f"  NBlk.eq_of_getD_rows ({x}_Dl.trans {x}_Xr.symm) fun a ha => by\n"
                 f"    rw [{x}_Dl] at ha\n    exact {match_rows(m, x + '_D')}\n\n"
                 f"theorem S{r_}_sok : Cert3.SOK S{r_} {x} :=\n"
                 f"  Cert3.SOK.intro ({x}_hD.trans (NBlk.expandΔ_eq {x} {x}_hE).symm) {x}_ok {x}_z\n")
        files[f"ChkN{r_}.lean"] = hd([f"{NS}.Data"],
                                     f"N = 5, s = 2: the SOS block `S{r_}` is the expansion of the checked facially "
                                     f"reduced block `{x}`\n(m, r = {m}, {r}).  Row-wise kernel checks (one `decide` "
                                     "per row), as in `lean/gen_log/gen_capchk.py` of alejandrozarco/thomson-n7-log.") + ns("".join(B))
    # ---------------- Check.lean
    tot = rep["total"]
    names = ["H"] + [f"F{k}" for k in range(K)] + [f"S{r_}" for r_ in range(nS)]
    fok = "".join(f".cons F{k}_fok (" for k in range(K)) + ".nil" + ")" * K
    sok = "".join(f".cons S{r_}_sok (" for r_ in range(nS)) + ".nil" + ")" * nS
    body = (f"theorem cf_K : cf.K = {K} := rfl\n\n"
            f"theorem cf_S : cf.S = {llist(f'S{r_}' for r_ in range(nS))} := rfl\n\n"
            f"theorem range_K : List.range {K} = {llist(range(K))} := rfl\n\n"
            f"/-- The statistics of the whole identity expression: `ℓ¹`-norm below `2 ^ {w}`, degrees "
            f"`{tot[1]}, {tot[2]}, {tot[3]}`, Kronecker value `0`. -/\n"
            f"theorem idE_stat : ThomsonN7.Case1.c1Stat {w} {D} cf.idE = ({tot[0]}, {tot[1]}, {tot[2]}, {tot[3]}, (0 : Int)) := by\n"
            "  rw [ThomsonN7.Case1.c1Stat_idE, cf_K, cf_S, range_K]\n"
            "  simp only [List.map_cons, List.map_nil]\n"
            f"  rw [{', '.join(f'stat_{nm}' for nm in names)}]\n"
            "  decide +kernel\n\n"
            "/-- The Kronecker check of the identity expression. -/\n"
            "theorem cf_chk : chk cf.idE = true := by\n"
            f"  have h := ThomsonN7.Case1.c1Stat_eq {w} {D} cf.idE\n"
            "  rw [idE_stat] at h\n"
            "  simp only [Prod.mk.injEq] at h\n"
            "  obtain ⟨hl, hx, hy, hz, hk⟩ := h\n"
            "  unfold chk\n"
            "  rw [← hl, ← hx, ← hy, ← hz]\n"
            f"  have hW : Nat.log2 {tot[0]} + 1 = {w} := by decide +kernel\n"
            f"  have hD : max {tot[1]} (max {tot[2]} {tot[3]}) + 1 = {D} := by decide +kernel\n"
            "  rw [hW, hD]\n"
            "  exact decide_eq_true hk.symm\n\n"
            "/-- The kernel blocks are the expansions of the checked witnesses. -/\n"
            f"theorem cf_hF : List.Forall₂ Cert3.FOK cf.F {llist(f'nF{k}' for k in range(K))} :=\n  {fok}\n\n"
            "/-- The SOS blocks are the expansions of the checked witnesses. -/\n"
            f"theorem cf_hS : List.Forall₂ Cert3.SOK cf.S {llist(f'nS{r_}' for r_ in range(nS))} :=\n  {sok}\n")
    files["Check.lean"] = hd(["ThomsonGen.Case1Stat", f"{NS}.ChkF"] + [f"{NS}.ChkS{r_}" for r_ in range(nS)]
                             + [f"{NS}.ChkN{r_}" for r_ in range(nS)],
                             f"N = 5, s = 2: assembly of the chunked checks.  `chk cf.idE = true` (ℓ¹ < 2^{w}, degrees "
                             f"< {D}, Kronecker value 0;\nsoundness: `Kron.Ex.ev_eq_zero_of_kev`), and the block facts "
                             "`List.Forall₂ Cert3.FOK cf.F _`, `List.Forall₂ Cert3.SOK cf.S _`\n"
                             "(the composition mirrors upstream `Case1.lean`; the piece statistics are named constants "
                             "so that the big literals\nstay out of the elaborated terms).\n\nAttribution: adapted "
                             "from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream): "
                             "`cf_chk` ← `Case1.cf_chk`.") + ns(body)
    # ---------------- Bound.lean
    Hm = [Fr(x, data["Lam"]) for x in data["h"]]
    def rlit(q):
        return f"({q.numerator} : ℝ)" if q.denominator == 1 else f"({q.numerator} / {q.denominator} : ℝ)"
    terms = " +\n    ".join(rlit(q) if j == 0 else f"{rlit(q)} * x" if j == 1 else f"{rlit(q)} * x ^ {j}"
                               for j, q in enumerate(Hm))
    gd = "".join(f"  have g{j} : h_.getD {j} 0 = {lint(data['h'][j])} := rfl\n" for j in range(len(Hm)))
    body = (
        "open scoped RealInnerProductSpace\n\n"
        "/-- The degree-10 minorant `H` of the certificate, in the monomial basis (exact rationals). -/\n"
        f"noncomputable def Hn (x : ℝ) : ℝ :=\n    {terms}\n\n"
        "/-- `Hn` is the minorant `cf.Hf` of the checked certificate. -/\n"
        "theorem Hn_eq (x : ℝ) : Hn x = cf.Hf x := by\n"
        + gd +
        f"  have e : cf.Hf x = (∑ j ∈ Finset.range {len(Hm)}, ((h_.getD j 0 : ℤ) : ℝ) * x ^ j) / ((lam_ : ℕ) : ℝ) := rfl\n"
        "  rw [e]\n"
        f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero, {', '.join(f'g{j}' for j in range(len(Hm)))}]\n"
        "  unfold Hn lam_\n"
        "  push_cast\n"
        "  ring\n\n"
        "theorem lam_pos : 0 < cf.Lam := by decide +kernel\n\n"
        "theorem eps_div : (cf.eps : ℝ) / (cf.Lam : ℝ) = 17 / 4 := by\n"
        f"  have h1 : cf.eps = {lint(data['eps'])} := rfl\n"
        f"  have h2 : cf.Lam = {data['Lam']} := rfl\n"
        "  rw [h1, h2]\n"
        "  norm_num\n\n"
        "theorem cut : ((cf.an : ℤ) : ℝ) / ((cf.ad : ℕ) : ℝ) ≤ -1 := by\n"
        "  have h1 : cf.an = -1 := rfl\n"
        "  have h2 : cf.ad = 1 := rfl\n"
        "  rw [h1, h2]\n"
        "  norm_num\n\n"
        "/-- **The three-point bound for `N = 5`.**  For all unit vectors `x 0, …, x 4` of `ℝ³`,\n"
        "`17/4 ≤ ∑_{i<j} Hn ⟪x i, x j⟫`. -/\n"
        "theorem bound (x : Fin 5 → R3) (hx : ∀ i, ‖x i‖ = 1) :\n"
        "    (17 / 4 : ℝ) ≤ ∑ i, ∑ j ∈ Finset.Ioi i, Hn ⟪x i, x j⟫ := by\n"
        f"  have h := Cert3.soundN cf {llist(f'nF{k}' for k in range(K))} {llist(f'nS{r_}' for r_ in range(nS))}\n"
        "    cf_hF cf_hS (by decide +kernel) lam_pos (by decide +kernel) cf_chk cut x hx\n"
        "  rw [eps_div] at h\n"
        "  simp only [Hn_eq]\n"
        "  exact h\n")
    files["Bound.lean"] = hd([f"{NS}.Check"],
                             "N = 5, Riesz s = 2: the three-point bound `17/4 ≤ ∑_{i<j} H(⟪x i, x j⟫)` for five unit "
                             "vectors of `ℝ³`,\nfrom the checked facially reduced certificate `cf` and "
                             "`ThomsonN7.Cert.Cert3.soundN`.  `Hn` is `H` written out\nin the monomial basis "
                             "(`Hn_eq`).  The comparison `H ≤ φ₂` is not part of this module.") + \
        f"open Real\n\nnamespace {NS}\nopen ThomsonN7 ThomsonN7.Cert ThomsonN7.Cert.Cert3\n\n" + body + f"\nend {NS}\n"
    for nm, txt in files.items():
        with open(os.path.join(outdir, nm), "w") as fh:
            fh.write(txt)
    return files


def stored_data(data):
    FD = [nb.expandD() for nb in data["NF"]]
    SD = [nb.expandD() for nb in data["NSB"]]
    SE = [entMat(nb.inner()) for nb in data["NSB"]]
    SDw = [width([v for row in X for v in row]) for X in SD]
    SEw = [width([v for row in E for v in row]) for E in SE]
    return FD, SD, SDw, SE, SEw


# ====================================================================== --check: parse the emitted files
HEX = r"(0x[0-9a-f]+|\d+)"


def _num(s): return int(s, 16) if s.startswith("0x") else int(s)


def parse_mat(s):
    s = s.strip()
    assert s.startswith("[[") or s == "[]", s[:40]
    return [[int(v) for v in row.split(",") if v.strip()] for row in re.findall(r"\[([-0-9, ]*)\]", s[1:-1])]


def parse(outdir):
    txt = open(os.path.join(outdir, "Data.lean"), encoding="utf-8").read()
    data = {}
    data["h"] = [int(v) for v in re.search(r"def h_ : List Int := \[([-0-9, ]*)\]", txt).group(1).split(",")]
    data["Lam"] = int(re.search(r"def lam_ : Nat := (\d+)", txt).group(1))
    data["eps"] = int(re.search(r"def eps_ : Int := \((-?\d+) : Int\)", txt).group(1))
    cfm = re.search(r"def cf : Cert3 :=\s+\{ n := (\d+), Lam := lam_, an := (-?\d+), ad := (\d+), h := h_, "
                    r"eps := eps_,\s+F := \[([A-Za-z0-9_, ]*)\],\s+S := \[([A-Za-z0-9_, ]*)\] \}", txt)
    data["n"], data["an"], data["ad"] = int(cfm.group(1)), int(cfm.group(2)), int(cfm.group(3))
    Fn = [x.strip() for x in cfm.group(4).split(",")]
    Sn = [x.strip() for x in cfm.group(5).split(",")]
    nbs = {}
    for mt in re.finditer(r"def (\S+) : NBlk :=\s+⟨(\[.*?\]), (\d+), (\d+), (\d+), (\d+),\s+" + HEX + r",\s+" + HEX
                          + r",\s+" + HEX + "⟩", txt, re.S):
        nbs[mt.group(1)] = NBlk(parse_mat(mt.group(2)), *map(int, mt.group(3, 4, 5, 6)),
                                *(_num(mt.group(i)) for i in (7, 8, 9)))
    lits = {mt.group(1): parse_mat(mt.group(2)) for mt in
            re.finditer(r"def (\S+) : List \(List Int\) := (\[\[.*?\]\])\n", txt, re.S)}
    packs = {mt.group(1): unpackM(int(mt.group(2)), int(mt.group(3)), int(mt.group(4)), _num(mt.group(5))) for mt in
             re.finditer(r"def (\S+) : List \(List Int\) := unpackM (\d+) (\d+) (\d+)\s+" + HEX, txt)}
    zs = {mt.group(1): [tuple(int(y) for y in t.split(",")) for t in re.findall(r"\(([0-9, ]+)\)", mt.group(2))]
          for mt in re.finditer(r"def (\S+) : List \(Nat × Nat × Nat\) := (\[.*?\])\n", txt)}
    blks = {mt.group(1): mt.group(2) for mt in re.finditer(r"def (\S+) : Blk := ⟨\[\], \[\], (\S+)⟩", txt)}
    sbl = {mt.group(1): ([int(v) for v in mt.group(2).split(",") if v.strip()], int(mt.group(3)), mt.group(4), mt.group(5))
           for mt in re.finditer(r"def (\S+) : SBlk := ⟨\[([0-9, ]*)\], (\d+), (\S+), (\S+)⟩", txt)}
    FD = [lits[blks[f]] for f in Fn]
    data["NF"] = [nbs["n" + f] for f in Fn]
    SD, data["NSB"], data["codes"], data["z"] = [], [], [], []
    for s in Sn:
        g, sig, zn, bn = sbl[s]
        assert sig == 0
        SD.append(packs[blks[bn]])
        data["codes"].append(g)
        data["z"].append(zs[zn])
        data["NSB"].append(nbs["n" + s])
    SE = []
    for r_ in range(len(Sn)):
        t = open(os.path.join(outdir, f"ChkN{r_}.lean"), encoding="utf-8").read()
        mt = re.search(r"def nS%d_E : List \(List ℤ\) := unpackM (\d+) (\d+) (\d+)\s+" % r_ + HEX, t)
        SE.append(unpackM(int(mt.group(1)), int(mt.group(2)), int(mt.group(3)), _num(mt.group(4))))
    stats = {}
    for fn in sorted(os.listdir(outdir)):
        if fn.startswith("Chk") and fn.endswith(".lean"):
            t = open(os.path.join(outdir, fn), encoding="utf-8").read()
            for mt in re.finditer(r"def stat(\S+) : ThomsonN7\.Case1\.C1Stat :=\s+\((\d+), (\d+), (\d+), (\d+), "
                                  r"\((-?)(0x[0-9a-f]+) : Int\)\)", t):
                kv = int(mt.group(7), 16) * (-1 if mt.group(6) else 1)
                stats[mt.group(1)] = (int(mt.group(2)), int(mt.group(3)), int(mt.group(4)), int(mt.group(5)), kv)
            for mt in re.finditer(r"ThomsonN7\.Case1\.c1Stat (\d+) (\d+) ", t):
                stats.setdefault("_wD", set()).add((int(mt.group(1)), int(mt.group(2))))
    chk = open(os.path.join(outdir, "Check.lean"), encoding="utf-8").read()
    return data, FD, SD, SE, stats, chk


def check_emitted(outdir, J=None):
    data, FD, SD, SE, stats, chk = parse(outdir)
    ok = True
    log(f"parsed: n = {data['n']}, Λ = {data['Lam']} ({data['Lam'].bit_length()} bits), an/ad = {data['an']}/{data['ad']}, "
        f"|h| = {len(data['h'])}, F sizes {[(len(nb.N), nb.r) for nb in data['NF']]}, "
        f"S sizes {[(len(z), nb.r) for z, nb in zip(data['z'], data['NSB'])]}")
    rep = simulate(data, FD, SD, SE)
    log(f"n ≥ 3: {rep['n_ge_3']}, Λ > 0: {rep['Lam_pos']}, ad > 0: {rep['ad_pos']}, an/ad ≤ -1: {rep['cut']}")
    log(f"FOK (okN, F_D = expandΔ): {rep['FOK']}")
    for r_, p in enumerate(rep["SOK"]):
        log(f"SOK S{r_}: {'all true' if all(p.values()) else p}")
    w, D = rep["w"], rep["D"]
    wd = stats.pop("_wD", set())
    good = wd == {(w, D)}
    log(f"Kronecker parameters in the emitted statements: {sorted(wd)}; recomputed (w, D) = ({w}, {D}): "
        f"{'MATCH' if good else 'MISMATCH'}")
    ok &= good
    for nm, s in rep["stats"].items():
        g = stats.get(nm) == s
        ok &= g
        log(f"  stat{nm}: {'MATCH' if g else 'MISMATCH'} (ℓ¹ {s[0].bit_length()} bits, deg {s[1:4]}, "
            f"|kev| {abs(s[4]).bit_length()} bits)")
    tot = rep["total"]
    g = (f"c1Stat {w} {D} cf.idE = ({tot[0]}, {tot[1]}, {tot[2]}, {tot[3]}, (0 : Int))" in chk and tot[4] == 0
         and f"Nat.log2 {tot[0]} + 1 = {w}" in chk and f"max {tot[1]} (max {tot[2]} {tot[3]}) + 1 = {D}" in chk)
    ok &= g
    log(f"composition: total ℓ¹ = {tot[0]} ({tot[0].bit_length()} bits) < 2^{w}: {tot[0] < (1 << w)}, "
        f"Nat.log2 ℓ¹ + 1 = {nat_log2(tot[0]) + 1}, degrees {tot[1:4]}, kev(idE) = "
        f"{tot[4] if tot[4] == 0 else 'NONZERO'}; Check.lean literals {'MATCH' if g else 'MISMATCH'}")
    ok &= rep["ok"]
    if J is not None:
        cc = json_crosscheck(data, FD, SD, J)
        log(f"JSON cross-check (exact rationals): {cc}")
        ok &= all(cc.values())
    sizes = {fn: os.path.getsize(os.path.join(outdir, fn)) for fn in sorted(os.listdir(outdir)) if fn.endswith(".lean")}
    log(f"module sizes (bytes): {sizes}")
    log("CHECK " + ("ALL_OK" if ok else "FAILED"))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json", nargs="?")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--json", dest="json2")
    ap.add_argument("--outdir", default=DEF_OUT)
    a = ap.parse_args()
    if a.check:
        jp = a.json2 or a.json
        sys.exit(0 if check_emitted(a.outdir, json.load(open(jp)) if jp else None) else 1)
    raw = open(a.json, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    J = json.loads(raw)
    data = build(J)
    FD, SD, SDw, SE, SEw = stored_data(data)
    rep = simulate(data, FD, SD, SE)
    log(f"simulation: ok = {rep['ok']}, w = {rep['w']}, D = {rep['D']}, kev(idE) = {rep['total'][4]}")
    if not rep["ok"]:
        raise SystemExit("simulated Lean checks FAILED; nothing emitted")
    cc = json_crosscheck(data, FD, SD, J)
    log(f"JSON cross-check: {cc}")
    if not all(cc.values()):
        raise SystemExit("integer data differ from the JSON; nothing emitted")
    files = emit(data, rep, os.path.basename(a.json), sha, a.outdir, FD, SD, SDw, SE, SEw)
    for nm, txt in files.items():
        log(f"  wrote {os.path.join(a.outdir, nm)} ({len(txt.encode())} bytes)")
    sys.exit(0 if check_emitted(a.outdir, J) else 1)


if __name__ == "__main__":
    main()
