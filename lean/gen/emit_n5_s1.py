#!/usr/bin/env python3
"""emit_n5_s1.py -- N = 5, Coulomb (Riesz s = 1): exact three-point certificate over K = Q(sqrt2, sqrt3) -> Lean.

usage (run with `nice -n 19`):
  python3 emit_n5_s1.py cert_n5_s1_short.json [--bits 32] [--outdir DIR]   emit, then run --check on the output
  python3 emit_n5_s1.py --check [--outdir DIR] [--json cert_n5_s1_short.json]
                                re-read the EMITTED .lean files and re-run, in Python, every Lean Bool check in them

Semantics of the JSON (check/check_n5_odd.py of this repository): every number is [a, b, c, d] = a + b√2 + c√3 + d√6 (the √6
parts are all 0 and are asserted to be), and
  (H(u)+H(v)+H(t))/3 - e/10 - R[F] = Σ_r g_r z_rᵀ B_r z_r     in K[u, v, t],
with rational structure (reducers N_k, M_r, multipliers g_r, monomials z_r).  The identity is K-linear in the numerical
data (H, e, F′, B′), so its component c ∈ {0: 1, 1: √2, 2: √3} is the identity of the rational component data.

Lean layout (default DIR = thomson-n7-log-macbuild/lean/N5R1, modules `N5R1.*`; generic part
ThomsonGen/Cert/Cert3K.lean):
  Data.lean    common denominator Λ = lam_; component certificates `cf0, cf1, cf2 : Cert3` (n = 5, no cut, h = Λ·H_c,
               eps = Λ·e_c, EXPANDED component blocks `⟨[], [], X⟩`, X = Ñ·E_c·Ñᵀ, E_c = Λ·B̃_c); `cfK c`.
  Blocks.lean  the corners κ_j = 2^B·(1, ℓ₂ or h₂, ℓ₃ or h₃) of the box [ℓ₂, h₂] × [ℓ₃, h₃] ∋ (√2, √3) (dyadic, width
               2^-B); per block: integer basis Ñ, component reduced blocks E_0..E_2, ONE LDLᵀ (d, l) shared by the
               corners with its product P = Σ_q d_q l_q l_qᵀ, and per corner the remainder R_j = Σ_c κ_jc E_c - P.
  ChkI<c>.lean Kronecker statistics of the 13 pieces of cf<c>.idE (upstream Case1Stat machinery).
  ChkF.lean    kernel blocks: X = expandE Ñ E_c, X symmetric, KOK (corners).
  ChkS<r>.lean SOS block r: X rows = expandE Ñ E_c rows (c = 0, 1, 2), ldl d l = P (rows), KOK (corners).
  Check.lean   chk cf<c>.idE = true (composition of the piece statistics).
  Bound.lean   the weights w = (1, √2, √3) lie in the box (KB.AffOK, via N5R1.Corner), positivity of the weighted
               blocks, Cert3K.soundK, and `N5R1.bound : 1/2 + 3√2 + √3 ≤ Σ_{i<j} Hn ⟪x i, x j⟫`,
               Hn = Hn0 + √2·Hn1 + √3·Hn2 (monomial form, exact rationals).
The Python mirror of the Lean definitions (Kron.Ex, Cert3, c1Stat, NBlk list arithmetic, okF, packing) is imported
from lean/gen/emit_n5.py; `lin` and `expandE` (Cert3K.lean) are mirrored here.
"""
import argparse, hashlib, itertools, json, os, re, sys, time
from fractions import Fraction as Fr
from math import lcm, isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import emit_n5 as E5          # noqa: E402

sys.setrecursionlimit(1000000)
T0 = time.time()
DEF_OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "N5R1")
NS = "N5R1"
Q = 3                                        # components 1, √2, √3
SQ = (1, 2, 3)                               # θ_c² ... θ_0 = 1, θ_1 = √2, θ_2 = √3
SCRIPT = "lean/gen/emit_n5_s1.py"
SPLIT = {0: [[0, 1], [2, "K"]]}            # SOS block 0 (56 × 49): two check modules


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


# ====================================================================== mirrors of Cert3K.lean
def lin(kappa, Ms):
    """KB.lin: `lin (a :: as) (M :: Ms) = matAdd (matScale a M) (lin as Ms)`, `lin _ _ = []`."""
    out = []
    for a, M in reversed(list(zip(kappa, Ms))):
        out = E5.matAdd([E5.pscale(a, row) for row in M], out)
    return out


def expandE(N, E):
    """KB.expandE: `N.map fun row => N.map fun rb => dot (vecMat row E) rb`."""
    return [[E5.dot(E5.vecMat(row, E), rb) for rb in N] for row in N]


def okF(r, d, l, D): return E5.okF(r, E5.Blk(d, l, D))


# ====================================================================== JSON -> integer data
def kcomp(z):
    v = [Fr(x) for x in z]
    assert len(v) == 4 and v[3] == 0, "nonzero √6 component"
    return v[:3]


def H_monomial_c(J, c):
    Hc = [kcomp(z)[c] for z in J["H_chebyshev"]]
    out = [Fr(0)] * len(Hc)
    for j, cj in enumerate(Hc):
        for i, x in enumerate(E5.cheb_mono(j)):
            out[i] += cj * x
    return out


def shared_ldl(Mks, s=40):
    """one LDLᵀ (d, l) for all corner matrices Mks (integers): float Cholesky of the mean minus half its least
    eigenvalue, l rounded to 2^-s (unit diagonal 2^s), d = floor(pivot / 4^s); P = Σ d_q l_q l_qᵀ."""
    import numpy as np
    r = len(Mks[0])
    if r == 0:
        return [], [], [], 1.0
    scale = max(abs(x) for M in Mks for row in M for x in row)
    sh = max(0, scale.bit_length() - 900)
    A = np.array([[sum(float(M[a][b] >> sh) for M in Mks) / len(Mks) for b in range(r)] for a in range(r)])
    sf = float(scale >> sh)
    A = A / sf
    lam = np.linalg.eigvalsh(A)[0]
    assert lam > 0, lam
    Lc = np.linalg.cholesky(A - (lam / 2) * np.eye(r))
    dd = np.diag(Lc) ** 2
    Lu = Lc / np.diag(Lc)
    l = [[0] * r for _ in range(r)]
    for q in range(r):
        l[q][q] = 1 << s
        for a in range(q + 1, r):
            l[q][a] = int(round(Lu[a, q] * 2.0 ** s))
    d = [int(Fr(float(dd[q])) * Fr(scale) / (1 << (2 * s))) for q in range(r)]
    assert all(x >= 0 for x in d)
    P = E5.ldl(d, l)
    return d, l, P, lam


def build(J, bits):
    assert J["n"] == 5 and J["D"] == 10
    e = kcomp(J["e"])
    assert e == [Fr(1, 2), Fr(3), Fr(1)], e
    Hm = [H_monomial_c(J, c) for c in range(Q)]
    blocks = []
    for kind, Ns, Bs in (("F", J["F_reducers"], J["F_reduced"]), ("S", J["sos_reducers"], J["sos_reduced"])):
        for idx, (N, Bp) in enumerate(zip(Ns, Bs)):
            Nq = [[Fr(x) for x in row] for row in N]
            Ni, cs = E5.int_cols(Nq)
            Bt = [[[kcomp(z)[c] / (cs[i] * cs[j]) for j, z in enumerate(row)] for i, row in enumerate(Bp)]
                  for c in range(Q)]
            blocks.append(dict(kind=kind, idx=idx, m=len(Nq), r=len(Bp), N=Ni, Bt=Bt))
    assert [b["m"] for b in blocks if b["kind"] == "F"] == [6, 5, 4, 3]
    assert J["sos_degrees"] == [5, 4, 4, 4, 4, 4, 4, 3] and len(J["sos_g"]) == 8
    L = 1
    for c in range(Q):
        for x in Hm[c] + [e[c]]:
            L = lcm(L, x.denominator)
    for b in blocks:
        for c in range(Q):
            for row in b["Bt"][c]:
                for x in row:
                    L = lcm(L, x.denominator)
    log(f"Λ = lcm of all denominators (all components): {L.bit_length()} bits")
    D = 1 << bits
    a2, a3 = isqrt(2 * D * D), isqrt(3 * D * D)
    assert a2 * a2 < 2 * D * D < (a2 + 1) ** 2 and a3 * a3 < 3 * D * D < (a3 + 1) ** 2
    kap = [[D, a2 + i, a3 + j] for i in (0, 1) for j in (0, 1)]          # order: (b0, b1) = (lo,lo),(lo,hi),(hi,lo),(hi,hi)
    data = dict(Lam=L, bits=bits, kap=kap, h=[[int(x * L) for x in Hm[c]] for c in range(Q)],
                eps=[int(e[c] * L) for c in range(Q)], blocks=blocks,
                codes=[E5.GCODES[g] for g in J["sos_g"]], z=[E5.monos_upto(d) for d in J["sos_degrees"]])
    for b in blocks:
        b["E"] = [[[int(x * L) for x in row] for row in b["Bt"][c]] for c in range(Q)]
        assert all(Fr(b["E"][c][i][j]) == b["Bt"][c][i][j] * L for c in range(Q) for i in range(b["r"])
                   for j in range(b["r"]))
        b["X"] = [expandE(b["N"], b["E"][c]) for c in range(Q)]
        Mks = [lin(k, b["E"]) for k in kap]
        d, l, P, lam = shared_ldl(Mks)
        b["d"], b["l"], b["P"] = d, l, P
        b["R"] = [[[Mk[i][j] - P[i][j] for j in range(b["r"])] for i in range(b["r"])] for Mk in Mks]
        ok = [okF(b["r"], d, l, R) for R in b["R"]]
        slack = [min(R[i][i] - sum(abs(R[i][j]) for j in range(b["r"]) if j != i) for i in range(b["r"])) /
                 max(abs(x) for x in itertools.chain(*Mk)) for R, Mk in zip(b["R"], Mks)]
        log(f"  {b['kind']}{b['idx']}: {b['m']} × {b['r']}; min eig (normalised) {lam:.2e}; okF at the 4 corners "
            f"{ok}; min relative DD slack {min(slack):.2e}")
        assert all(ok)
    return data


def cert_of(data, c):
    F = [E5.Blk([], [], b["X"][c]) for b in data["blocks"] if b["kind"] == "F"]
    S = [E5.SBlk(cd, 0, z, E5.Blk([], [], b["X"][c]))
         for cd, z, b in zip(data["codes"], data["z"], [b for b in data["blocks"] if b["kind"] == "S"])]
    return E5.Cert3(5, data["Lam"], -1, 1, data["h"][c], data["eps"][c], F, S)


# ====================================================================== simulation of every Lean Bool check
def simulate(data):
    rep, ok = {}, True
    rep["Lam_pos"] = data["Lam"] > 0
    ok &= rep["Lam_pos"]
    rep["ident"] = []
    for c in range(Q):
        cf = cert_of(data, c)
        pcs = E5.pieces(cf)
        lst = {nm: E5.stat_l(e) for nm, e in pcs}
        z0 = lambda nm: lst[nm] + (0,)
        tot0 = E5.compose_idE(cf, z0("H"), [z0(f"F{k}") for k in range(cf.K)], [z0(f"S{i}") for i in range(len(cf.S))])
        w, D = E5.chk_params(*tot0[:4])
        st = {nm: lst[nm] + (E5.kev(e, w, D),) for nm, e in pcs}
        tot = E5.compose_idE(cf, st["H"], [st[f"F{k}"] for k in range(cf.K)], [st[f"S{i}"] for i in range(len(cf.S))])
        good = tot[4] == 0 and E5.chk_params(*tot[:4]) == (w, D)
        rep["ident"].append(dict(w=w, D=D, stats=st, total=tot, chk=good))
        ok &= good
        log(f"  component {c}: Kronecker w = {w}, D = {D}, ℓ¹ {tot[0].bit_length()} bits, kev(idE) = "
            f"{tot[4] if tot[4] == 0 else 'NONZERO'}")
    rep["blocks"] = []
    for b in data["blocks"]:
        r, m = b["r"], b["m"]
        p = dict()
        p["X"] = all(b["X"][c] == expandE(b["N"], b["E"][c]) for c in range(Q))
        p["Xlen"] = all(len(b["X"][c]) == m for c in range(Q)) and len(expandE(b["N"], b["E"][0])) == m
        if b["kind"] == "F":
            p["Xsym"] = all([row[:m] for row in b["X"][c]] == E5.transposeSq(m, b["X"][c]) for c in range(Q))
        p["hN"] = all(len(row) <= r for row in b["N"])
        p["hE"] = all(len(E) <= r and all(len(row) <= r for row in E) for E in b["E"])
        p["hq"] = len(b["E"]) <= Q
        p["P"] = E5.ldl(b["d"], b["l"]) == b["P"] and len(b["P"]) == r
        p["corners"] = all(len(k) <= Q and okF(r, b["d"], b["l"], R) and len(b["d"]) <= r and len(b["l"]) <= r
                           and E5.matAdd(b["P"], R) == lin(k, b["E"]) for k, R in zip(data["kap"], b["R"]))
        p["m_le_N"] = m <= len(b["N"])
        rep["blocks"].append(p)
        ok &= all(p.values())
    rep["ok"] = ok
    return rep


def json_crosscheck(data, J):
    """the integer data / Λ equal the JSON numbers exactly (per component)."""
    L, out = data["Lam"], {}
    out["H"] = all([Fr(x, L) for x in data["h"][c]] == H_monomial_c(J, c) for c in range(Q))
    out["e"] = [Fr(x, L) for x in data["eps"]] == kcomp(J["e"])

    def NFNt(N, Fp, c):
        Nm = [[Fr(x) for x in row] for row in N]
        Fm = [[kcomp(z)[c] for z in row] for row in Fp]
        mm, r = len(Nm), len(Fm)
        NF = [[sum((Nm[i][k] * Fm[k][j] for k in range(r)), Fr(0)) for j in range(r)] for i in range(mm)]
        return [[sum((NF[i][k] * Nm[j][k] for k in range(r)), Fr(0)) for j in range(mm)] for i in range(mm)]
    Fb = [b for b in data["blocks"] if b["kind"] == "F"]
    Sb = [b for b in data["blocks"] if b["kind"] == "S"]
    out["F"] = all([[Fr(x, L) for x in row] for row in b["X"][c]] == NFNt(N, Fp, c)
                   for b, N, Fp in zip(Fb, J["F_reducers"], J["F_reduced"]) for c in range(Q))
    out["S"] = all([[Fr(x, L) for x in row] for row in b["X"][c]] == NFNt(N, Bp, c)
                   for b, N, Bp in zip(Sb, J["sos_reducers"], J["sos_reduced"]) for c in range(Q))
    gpoly = {"1": {(0, 0, 0): 1}, "1+u": {(0, 0, 0): 1, (1, 0, 0): 1}, "1+v": {(0, 0, 0): 1, (0, 1, 0): 1},
             "1+t": {(0, 0, 0): 1, (0, 0, 1): 1}, "1-u": {(0, 0, 0): 1, (1, 0, 0): -1},
             "1-v": {(0, 0, 0): 1, (0, 1, 0): -1}, "1-t": {(0, 0, 0): 1, (0, 0, 1): -1},
             "detG=1+2uvt-u^2-v^2-t^2": {(0, 0, 0): 1, (1, 1, 1): 2, (2, 0, 0): -1, (0, 2, 0): -1, (0, 0, 2): -1}}
    out["g"] = all(E5.poly_expand(E5.gE(-1, 1, cd)) == gpoly[g] for cd, g in zip(data["codes"], J["sos_g"]))
    out["z"] = all(z == E5.monos_upto(d) for z, d in zip(data["z"], J["sos_degrees"]))
    D = 1 << data["bits"]
    k = data["kap"]
    out["box"] = (all(x[0] == D for x in k) and k[0][1] == k[1][1] and k[2][1] == k[0][1] + 1 == k[3][1]
                  and k[0][2] == k[2][2] and k[1][2] == k[0][2] + 1 == k[3][2]
                  and k[0][1] ** 2 < 2 * D * D < k[2][1] ** 2 and k[0][2] ** 2 < 3 * D * D < k[1][2] ** 2)
    return out


# ====================================================================== Lean emission
def hexs(x): return f"0x{x:x}"
def lint(v): return f"({v} : Int)"
def llist(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
def lmat(M): return "[" + ", ".join(llist(row) for row in M) + "]"


def packed(name, M, rows, cols, ty="List (List ℤ)", doc=None):
    Bw = E5.width([v for row in M for v in row])
    d = f"/-- {doc} -/\n" if doc else ""
    return f"{d}def {name} : {ty} := unpackM {Bw} {cols} {rows}\n  {hexs(E5.packM(Bw, cols, M))}"


def packedI(name, v, doc=None):
    Bw = E5.width(v)
    d = f"/-- {doc} -/\n" if doc else ""
    return f"{d}def {name} : List ℤ := unpackI {Bw} {len(v)}\n  {hexs(E5.packI(Bw, v))}"


def stat_def(st):
    kv = st[4]
    kvs = f"(0x{kv:x} : Int)" if kv >= 0 else f"(-0x{-kv:x} : Int)"
    return f"({st[0]}, {st[1]}, {st[2]}, {st[3]}, {kvs})"


def header(imports, what, src, sha):
    return ("".join(f"import {i}\n" for i in imports)
            + f"/-! {what}\n\nGenerated by `{SCRIPT}` from `{src}`\n(sha256 {sha}).  Do not edit; regenerate. -/\n\n")


OPEN = ("open ThomsonN7 ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert ThomsonN7.Cert.Cert3 ThomsonN7.Cert.KB\n\n"
        "-- large literals: elaboration budget only (no effect on what is checked)\nset_option maxHeartbeats 0\n\n")


def match_rows(n, name):
    cases = "".join(f"\n      | {i}, _ => {name}{i}" for i in range(n))
    return f"match a, ha with{cases}\n      | _ + {n}, h => absurd h (by omega)"


def bname(b): return f"n{b['kind']}{b['idx']}"


def emit(data, rep, src, sha, outdir):
    os.makedirs(outdir, exist_ok=True)
    files = {}
    hd = lambda imports, what: header(imports, what, src, sha)
    ns = lambda body: f"namespace {NS}\n" + OPEN + body + f"\nend {NS}\n"
    Fb = [b for b in data["blocks"] if b["kind"] == "F"]
    Sb = [b for b in data["blocks"] if b["kind"] == "S"]
    K, nS = len(Fb), len(Sb)
    comp = ["1", "√2", "√3"]
    # ---------------- Data.lean
    L = [f"/-- The common denominator `Λ` of all components. -/\ndef lam_ : Nat := {data['Lam']}"]
    for c in range(Q):
        L.append(f"/-- `Λ · H_{c}` (the `{comp[c]}`-component of the minorant) in the monomial basis. -/\n"
                 f"def h{c}_ : List Int := {llist(data['h'][c])}")
        L.append(f"/-- `Λ · e_{c}`. -/\ndef eps{c}_ : Int := {lint(data['eps'][c])}")
    for b in Fb:
        k = b["idx"]
        for c in range(Q):
            L.append(f"/-- Kernel block `k = {k}`, component `{comp[c]}`, expanded: `Λ · N F′ Nᵀ` ({b['m']} × {b['m']}). -/\n"
                     f"def F{k}_D{c} : List (List Int) := {lmat(b['X'][c])}")
            L.append(f"def F{k}_{c} : Blk := ⟨[], [], F{k}_D{c}⟩")
    for b, cd, z in zip(Sb, data["codes"], data["z"]):
        r_ = b["idx"]
        zs = "[" + ", ".join(f"({a}, {bb}, {cc})" for a, bb, cc in z) + "]"
        L.append(f"def S{r_}_z : List (Nat × Nat × Nat) := {zs}")
        for c in range(Q):
            L.append(packed(f"S{r_}_D{c}", b["X"][c], b["m"], b["m"], "List (List Int)",
                            f"SOS block `r = {r_}`, component `{comp[c]}`, expanded Gram matrix `Λ · M B′ Mᵀ` "
                            f"({b['m']} × {b['m']})."))
            L.append(f"def S{r_}_{c} : SBlk := ⟨{llist(cd)}, 0, S{r_}_z, ⟨[], [], S{r_}_D{c}⟩⟩")
    for c in range(Q):
        L.append(f"/-- The `{comp[c]}`-component certificate: `n = 5`, no cut, expanded component blocks. -/\n"
                 f"def cf{c} : Cert3 :=\n  {{ n := 5, Lam := lam_, an := -1, ad := 1, h := h{c}_, eps := eps{c}_,\n"
                 f"    F := {llist(f'F{k}_{c}' for k in range(K))},\n"
                 f"    S := {llist(f'S{r_}_{c}' for r_ in range(nS))} }}")
    L.append("/-- The component certificates, indexed by `c < 3` (`1, √2, √3`). -/\n"
             "def cfK (c : ℕ) : Cert3 := [cf0, cf1, cf2].getD c cf0")
    files["Data.lean"] = hd(["ThomsonGen.Cert.Cert3K"],
                            "N = 5, Coulomb (s = 1): the exact three-point certificate over `K = ℚ(√2, √3)`, as three "
                            "rational component\ncertificates in upstream's `Cert3` format (components `1, √2, √3`; the "
                            "`√6`-components are zero).  Blocks are the\nEXPANDED component blocks `⟨[], [], Ñ·E_c·Ñᵀ⟩` "
                            "(not positive semidefinite individually).\nMultiplier codes (`Cert.codeE`): `[]` = 1, `5` = "
                            "1+u, `7` = 1+v, `9` = 1+t, `4` = 1-u, `6` = 1-v, `8` = 1-t, `3` = Gram determinant.") \
        + ns("\n\n".join(L) + "\n")
    # ---------------- Blocks.lean
    D = 1 << data["bits"]
    L = []
    for j, k in enumerate(data["kap"]):
        L.append(f"def κ{j} : List ℤ := {llist(k)}")
    L.append(f"/-- The corners `2^{data['bits']} · (1, x₂, x₃)`, `x₂ ∈ {{ℓ₂, h₂}}`, `x₃ ∈ {{ℓ₃, h₃}}` (order: (ℓ₂, ℓ₃), "
             f"(ℓ₂, h₃), (h₂, ℓ₃), (h₂, h₃)). -/\ndef κs : List (List ℤ) := [κ0, κ1, κ2, κ3]")
    for b in data["blocks"]:
        x, r = bname(b), b["r"]
        L.append(f"/-- Block `{b['kind']}{b['idx']}`: integer basis `Ñ` ({b['m']} × {r}). -/\n"
                 f"def {x}_N : List (List ℤ) := {lmat(b['N'])}")
        for c in range(Q):
            L.append(packed(f"{x}_E{c}", b["E"][c], r, r, doc=f"Component `{comp[c]}` of the reduced block: `Λ · B̃_{c}`."))
        L.append(f"def {x}_Es : List (List (List ℤ)) := [{x}_E0, {x}_E1, {x}_E2]")
        L.append(packedI(f"{x}_d", b["d"], "Shared `LDLᵀ` pivots."))
        L.append(packed(f"{x}_l", b["l"], r, r, doc="Shared `LDLᵀ` columns (`l_q`, unit `2^s` at `q`)."))
        L.append(packed(f"{x}_P", b["P"], r, r, doc="`P = ∑_q d_q l_q l_qᵀ`."))
        for j in range(4):
            L.append(packed(f"{x}_R{j}", b["R"][j], r, r, doc=f"Remainder at corner `κ{j}`: `∑_c κ{j}_c E_c - P`."))
            L.append(f"def {x}_C{j} : Blk := ⟨{x}_d, {x}_l, {x}_R{j}⟩")
    files["Blocks.lean"] = hd(["ThomsonGen.Cert.Cert3K"],
                              "N = 5, Coulomb (s = 1): the facially reduced blocks over `K` and their corner witnesses.\n"
                              f"Box: `[ℓ₂, h₂] × [ℓ₃, h₃]` with `ℓ₂ = {data['kap'][0][1]} / 2^{data['bits']}`, "
                              f"`h₂ = ℓ₂ + 2^-{data['bits']}`, `ℓ₃ = {data['kap'][0][2]} / 2^{data['bits']}`, "
                              f"`h₃ = ℓ₃ + 2^-{data['bits']}`.\nPer block: basis `Ñ`, component reduced blocks "
                              "`E_c = Λ·B̃_c` (`c = 0, 1, 2`), one `LDLᵀ` `(d, l)` shared by the four corners\nwith "
                              "`P = ∑_q d_q l_q l_qᵀ`, and the corner blocks `C_j = ⟨d, l, R_j⟩`, "
                              "`R_j = ∑_c κ_{jc} E_c - P`.") + ns("\n\n".join(L) + "\n")
    # ---------------- ChkI<c>.lean
    for c in range(Q):
        ir = rep["ident"][c]
        w, Dk, st = ir["w"], ir["D"], ir["stats"]
        stmt = {"H": f"ThomsonN7.Case1.c1Stat {w} {Dk} (hE cf{c}.h)"}
        for k in range(K):
            stmt[f"F{k}"] = (f"ThomsonN7.Case1.c1Stat {w} {Dk} (ThomsonN7.Case1.c1FtotK cf{c}.n "
                             f"(fkE (cf{c}.m {k}) (cf{c}.blk {k}) {k}))")
        for r_ in range(nS):
            stmt[f"S{r_}"] = f"ThomsonN7.Case1.c1Stat {w} {Dk} (sblkE cf{c}.an cf{c}.ad S{r_}_{c})"

        def stat_block(nm):
            return (f"/-- Kronecker statistics `(ℓ¹, deg u, deg v, deg t, value)` of the piece `{nm}` of `cf{c}`. -/\n"
                    f"def stat{nm}_{c} : ThomsonN7.Case1.C1Stat :=\n  {stat_def(st[nm])}\n\n"
                    f"theorem stat_{nm}_{c} :\n    {stmt[nm]} = stat{nm}_{c} := by\n  decide +kernel\n")
        names = ["H"] + [f"F{k}" for k in range(K)] + [f"S{r_}" for r_ in range(nS)]
        files[f"ChkI{c}.lean"] = hd(["ThomsonGen.Case1Stat", f"{NS}.Data"],
                                    f"N = 5, Coulomb (s = 1): Kronecker statistics of the 13 pieces of the identity of "
                                    f"the `{comp[c]}`-component\ncertificate `cf{c}` (`w = {w}`, `D = {Dk}`).  One "
                                    "`decide +kernel` per piece.") + ns("\n".join(stat_block(nm) for nm in names))
    # ---------------- ChkF.lean and ChkS<r>.lean
    def kok_lines(b, rows_P):
        x, r = bname(b), b["r"]
        B = []
        if rows_P:
            B.append(f"theorem {x}_Pl : (NBlk.ldl {x}_d {x}_l).length = {r} := by decide +kernel")
            B.append(f"theorem {x}_Pr : {x}_P.length = {r} := by decide +kernel")
            for i in range(r):
                B.append(f"theorem {x}_P{i} : (NBlk.ldl {x}_d {x}_l).getD {i} [] = {x}_P.getD {i} [] := by decide +kernel")
            B.append(f"\ntheorem {x}_hP : NBlk.ldl {x}_d {x}_l = {x}_P :=\n"
                     f"  NBlk.eq_of_getD_rows ({x}_Pl.trans {x}_Pr.symm) fun a ha => by\n"
                     f"    rw [{x}_Pl] at ha\n    exact {match_rows(r, x + '_P')}\n")
        else:
            B.append(f"theorem {x}_hP : NBlk.ldl {x}_d {x}_l = {x}_P := by decide +kernel")
        for j in range(4):
            B.append(f"theorem {x}_ok{j} : okF {r} {x}_C{j} = true := by decide +kernel\n"
                     f"theorem {x}_lin{j} : NBlk.matAdd {x}_P {x}_R{j} = lin κ{j} {x}_Es := by decide +kernel\n"
                     f"theorem {x}_corner{j} : CornerOK 3 {r} {x}_Es κ{j} {x}_C{j} :=\n"
                     f"  ⟨by decide +kernel, {x}_ok{j}, by decide +kernel, by decide +kernel, by\n"
                     f"    rw [show NBlk.entMat {x}_C{j} = NBlk.matAdd (NBlk.ldl {x}_d {x}_l) {x}_R{j} from rfl, {x}_hP]\n"
                     f"    exact {x}_lin{j}⟩")
        B.append(f"/-- The checked `K`-block `{b['kind']}{b['idx']}`. -/\n"
                 f"theorem {x}_kok : KOK 3 {r} κs {x}_N {x}_Es [{x}_C0, {x}_C1, {x}_C2, {x}_C3] :=\n"
                 f"  ⟨by decide +kernel, by decide +kernel, by decide +kernel,\n"
                 f"    .cons {x}_corner0 (.cons {x}_corner1 (.cons {x}_corner2 (.cons {x}_corner3 .nil)))⟩")
        B.append(f"theorem {x}_mN : {b['m']} ≤ {x}_N.length := by decide +kernel")
        return B
    B = []
    for b in Fb:
        k, x, m = b["idx"], bname(b), b["m"]
        for c in range(Q):
            B.append(f"theorem F{k}_X{c} : F{k}_D{c} = expandE {x}_N {x}_E{c} := by decide +kernel")
            B.append(f"theorem F{k}_sym{c} : F{k}_D{c}.map (List.take {m}) = transposeSq {m} F{k}_D{c} := by decide +kernel")
        B += kok_lines(b, rows_P=False)
        B.append("")
    files["ChkF.lean"] = hd([f"{NS}.Data", f"{NS}.Blocks"],
                            "N = 5, Coulomb (s = 1): the kernel blocks `F0..F3`.  Expanded component blocks "
                            "`= Ñ·E_c·Ñᵀ` and symmetric;\nthe `K`-blocks with their corner witnesses (`KOK`).") \
        + ns("\n".join(B))
    chk_mods = []
    for b in Sb:
        r_, x, m, r = b["idx"], bname(b), b["m"], b["r"]
        parts = SPLIT.get(r_, [[0, 1, 2, "K"]])
        for pi, part in enumerate(parts):
            B = []
            for c in [p for p in part if p != "K"]:
                B.append(f"theorem S{r_}_Dl{c} : S{r_}_D{c}.length = {m} := by decide +kernel")
                B.append(f"theorem S{r_}_Xl{c} : (expandE {x}_N {x}_E{c}).length = {m} := by decide +kernel")
                for a in range(m):
                    B.append(f"theorem S{r_}_X{c}_{a} : S{r_}_D{c}.getD {a} [] = (expandE {x}_N {x}_E{c}).getD {a} [] := "
                             "by decide +kernel")
                B.append(f"\ntheorem S{r_}_X{c} : S{r_}_D{c} = expandE {x}_N {x}_E{c} :=\n"
                         f"  NBlk.eq_of_getD_rows (S{r_}_Dl{c}.trans S{r_}_Xl{c}.symm) fun a ha => by\n"
                         f"    rw [S{r_}_Dl{c}] at ha\n    exact {match_rows(m, f'S{r_}_X{c}_')}\n")
            if "K" in part:
                B += kok_lines(b, rows_P=True)
            nm = f"ChkS{r_}" + ("" if len(parts) == 1 else "abcdefgh"[pi])
            chk_mods.append(nm)
            what = ", ".join(f"`{comp[c]}`" for c in part if c != "K")
            if len(parts) == 1:
                doc = (f"N = 5, Coulomb (s = 1): SOS block `S{r_}` ({m} × {r}).  The expanded component blocks are "
                       "`Ñ·E_c·Ñᵀ`\n(row by row), and the `K`-block with its corner witnesses (`KOK`; `ldl d l = P` "
                       "row by row).")
                files[f"{nm}.lean"] = hd([f"{NS}.Data", f"{NS}.Blocks"], doc) + ns("\n".join(B) + "\n")
                continue
            files[f"{nm}.lean"] = hd([f"{NS}.Data", f"{NS}.Blocks"],
                                     f"N = 5, Coulomb (s = 1): SOS block `S{r_}` ({m} × {r}), part {pi + 1} of "
                                     f"{len(parts)}.  "
                                     + (f"The expanded component blocks ({what}) are `Ñ·E_c·Ñᵀ` (row by row)"
                                        if what else "")
                                     + (";\n" if what and "K" in part else ".\n" if what else "")
                                     + ("the `K`-block with its corner witnesses (`KOK`; `ldl d l = P` row by row)."
                                        if "K" in part else "")) + ns("\n".join(B) + "\n")
    # ---------------- Check.lean
    B = []
    for c in range(Q):
        ir = rep["ident"][c]
        w, Dk, tot = ir["w"], ir["D"], ir["total"]
        names = ["H"] + [f"F{k}" for k in range(K)] + [f"S{r_}" for r_ in range(nS)]
        B.append(f"theorem cf{c}_K : cf{c}.K = {K} := rfl\n\n"
                 f"theorem cf{c}_S : cf{c}.S = {llist(f'S{r_}_{c}' for r_ in range(nS))} := rfl\n\n"
                 f"/-- The statistics of the identity expression of `cf{c}`. -/\n"
                 f"theorem idE_stat{c} : ThomsonN7.Case1.c1Stat {w} {Dk} cf{c}.idE = "
                 f"({tot[0]}, {tot[1]}, {tot[2]}, {tot[3]}, (0 : Int)) := by\n"
                 f"  rw [ThomsonN7.Case1.c1Stat_idE, cf{c}_K, cf{c}_S, range_K]\n"
                 "  simp only [List.map_cons, List.map_nil]\n"
                 f"  rw [{', '.join(f'stat_{nm}_{c}' for nm in names)}]\n"
                 "  decide +kernel\n\n"
                 f"/-- The Kronecker check of the identity of `cf{c}`. -/\n"
                 f"theorem cf{c}_chk : chk cf{c}.idE = true := by\n"
                 f"  have h := ThomsonN7.Case1.c1Stat_eq {w} {Dk} cf{c}.idE\n"
                 f"  rw [idE_stat{c}] at h\n"
                 "  simp only [Prod.mk.injEq] at h\n"
                 "  obtain ⟨hl, hx, hy, hz, hk⟩ := h\n"
                 "  unfold chk\n"
                 "  rw [← hl, ← hx, ← hy, ← hz]\n"
                 f"  have hW : Nat.log2 {tot[0]} + 1 = {w} := by decide +kernel\n"
                 f"  have hD : max {tot[1]} (max {tot[2]} {tot[3]}) + 1 = {Dk} := by decide +kernel\n"
                 "  rw [hW, hD]\n"
                 "  exact decide_eq_true hk.symm\n")
    files["Check.lean"] = hd(["ThomsonGen.Case1Stat"] + [f"{NS}.ChkI{c}" for c in range(Q)] + [f"{NS}.ChkF"]
                             + [f"{NS}.{nm}" for nm in chk_mods],
                             "N = 5, Coulomb (s = 1): assembly of the chunked identity checks `chk cf<c>.idE = true` "
                             "(`c = 0, 1, 2`;\nthe composition mirrors upstream `Case1.lean`).\n\nAttribution: adapted from "
                             "huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream): "
                             "`cf0_chk`, `cf1_chk`, `cf2_chk` ← `Case1.cf_chk`.") \
        + ns(f"theorem range_K : List.range {K} = {llist(range(K))} := rfl\n\n" + "\n".join(B))
    # ---------------- Bound.lean
    files["Bound.lean"] = emit_bound(data, hd, Fb, Sb)
    for nm, txt in files.items():
        with open(os.path.join(outdir, nm), "w") as fh:
            fh.write(txt)
    return files


def rlit(q):
    return f"({q.numerator} : ℝ)" if q.denominator == 1 else f"({q.numerator} / {q.denominator} : ℝ)"


def emit_bound(data, hd, Fb, Sb):
    L_ = data["Lam"]
    bits = data["bits"]
    a2, a3 = data["kap"][0][1], data["kap"][0][2]
    out = []
    for c in range(Q):
        Hm = [Fr(x, L_) for x in data["h"][c]]
        terms = " +\n    ".join(rlit(q) if j == 0 else f"{rlit(q)} * x" if j == 1 else f"{rlit(q)} * x ^ {j}"
                                for j, q in enumerate(Hm))
        gd = "".join(f"  have g{j} : h{c}_.getD {j} 0 = {lint(data['h'][c][j])} := rfl\n" for j in range(len(Hm)))
        out.append(
            f"/-- The `{['1', '√2', '√3'][c]}`-component of the minorant, in the monomial basis (exact rationals). -/\n"
            f"noncomputable def Hn{c} (x : ℝ) : ℝ :=\n    {terms}\n\n"
            f"theorem Hn{c}_eq (x : ℝ) : Hn{c} x = cf{c}.Hf x := by\n" + gd +
            f"  have e : cf{c}.Hf x = (∑ j ∈ Finset.range {len(Hm)}, ((h{c}_.getD j 0 : ℤ) : ℝ) * x ^ j) / "
            "((lam_ : ℕ) : ℝ) := rfl\n"
            "  rw [e]\n"
            f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero, {', '.join(f'g{j}' for j in range(len(Hm)))}]\n"
            f"  unfold Hn{c} lam_\n  push_cast\n  ring\n")
    Fl = [b["m"] for b in Fb]
    body = (
        "open scoped RealInnerProductSpace\n\n"
        "/-- The weights `1, √2, √3` of the components. -/\n"
        "noncomputable def w : ℕ → ℝ := fun c => [1, √2, √3].getD c 0\n\n"
        f"/-- The kernel block sizes. -/\ndef mF : ℕ → ℕ := fun k => {llist(Fl)}.getD k 0\n\n"
        "def gs : ℕ → List ℕ := fun i => (cf0.S.getD i Cert3K.sDflt).g\n"
        "def σs : ℕ → ℕ := fun i => (cf0.S.getD i Cert3K.sDflt).σ\n"
        "def zs : ℕ → List (ℕ × ℕ × ℕ) := fun i => (cf0.S.getD i Cert3K.sDflt).z\n\n"
        f"theorem lo2 : (({a2} : ℝ) / {1 << bits}) ≤ √2 := by\n"
        f"  rw [show (({a2} : ℝ) / {1 << bits}) = √((({a2} : ℝ) / {1 << bits}) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]\n"
        "  exact Real.sqrt_le_sqrt (by norm_num)\n\n"
        f"theorem hi2 : √2 ≤ (({a2 + 1} : ℝ) / {1 << bits}) := by\n"
        f"  rw [show (({a2 + 1} : ℝ) / {1 << bits}) = √((({a2 + 1} : ℝ) / {1 << bits}) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]\n"
        "  exact Real.sqrt_le_sqrt (by norm_num)\n\n"
        f"theorem lo3 : (({a3} : ℝ) / {1 << bits}) ≤ √3 := by\n"
        f"  rw [show (({a3} : ℝ) / {1 << bits}) = √((({a3} : ℝ) / {1 << bits}) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]\n"
        "  exact Real.sqrt_le_sqrt (by norm_num)\n\n"
        f"theorem hi3 : √3 ≤ (({a3 + 1} : ℝ) / {1 << bits}) := by\n"
        f"  rw [show (({a3 + 1} : ℝ) / {1 << bits}) = √((({a3 + 1} : ℝ) / {1 << bits}) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]\n"
        "  exact Real.sqrt_le_sqrt (by norm_num)\n\n"
        "/-- A linear functional nonnegative at the four (scaled) corners of the box is nonnegative at `(1, √2, √3)`\n"
        "(`N5R1.affine_nonneg_of_corners`, with the third coordinate unused). -/\n"
        "theorem w_aff : AffOK 3 w κs := by\n"
        "  intro Q hQ\n"
        f"  have hD : (0 : ℝ) < {1 << bits} := by norm_num\n"
        "  have hk : ∀ κ ∈ κs, 0 ≤ (κ.getD 0 0 : ℝ) * Q 0 + (κ.getD 1 0 : ℝ) * Q 1 + (κ.getD 2 0 : ℝ) * Q 2 := by\n"
        "    intro κ hκ\n"
        "    have := hQ κ hκ\n"
        "    simpa [Finset.sum_range_succ] using this\n"
        "  have h00 := hk κ0 (by simp [κs])\n"
        "  have h01 := hk κ1 (by simp [κs])\n"
        "  have h10 := hk κ2 (by simp [κs])\n"
        "  have h11 := hk κ3 (by simp [κs])\n"
        "  simp only [κ0, κ1, κ2, κ3, List.getD_cons_zero, List.getD_cons_succ] at h00 h01 h10 h11\n"
        "  push_cast at h00 h01 h10 h11\n"
        f"  have key := N5R1.affine_nonneg_of_corners (Q 0) ![Q 1, Q 2, 0] ![{a2} / {1 << bits}, {a3} / {1 << bits}, 0]\n"
        f"    ![{a2 + 1} / {1 << bits}, {a3 + 1} / {1 << bits}, 0] ![√2, √3, 0]\n"
        "    (by intro i; fin_cases i <;> simp [lo2, lo3])\n"
        "    (by intro i; fin_cases i <;> simp [hi2, hi3])\n"
        "    (by\n"
        "      intro b\n"
        "      simp only [N5R1.aff, N5R1.corner, Fin.sum_univ_three]\n"
        "      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,\n"
        "        Matrix.tail_cons, zero_mul, add_zero, ite_self]\n"
        "      cases b 0 <;> cases b 1 <;> simp only [Bool.false_eq_true, ite_true, ite_false]\n"
        "      · have := div_nonneg h00 hD.le\n"
        "        convert this using 1; field_simp; ring\n"
        "      · have := div_nonneg h01 hD.le\n"
        "        convert this using 1; field_simp; ring\n"
        "      · have := div_nonneg h10 hD.le\n"
        "        convert this using 1; field_simp; ring\n"
        "      · have := div_nonneg h11 hD.le\n"
        "        convert this using 1; field_simp; ring)\n"
        "  simp only [N5R1.aff, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,\n"
        "    Matrix.head_cons, Matrix.tail_cons, zero_mul, add_zero] at key\n"
        "  simp only [Finset.sum_range_succ, Finset.sum_range_zero, w, List.getD_cons_zero, List.getD_cons_succ]\n"
        "  linarith\n\n"
        + "\n".join(out) + "\n"
        "/-- The minorant over `K`: `Hn = Hn0 + √2 · Hn1 + √3 · Hn2`. -/\n"
        "noncomputable def Hn (x : ℝ) : ℝ := Hn0 x + √2 * Hn1 x + √3 * Hn2 x\n\n"
        "theorem HK_eq (x : ℝ) : Cert3K.HK 3 cfK w x = Hn x := by\n"
        "  simp only [Cert3K.HK, Finset.sum_range_succ, Finset.sum_range_zero, w, List.getD_cons_zero,\n"
        "    List.getD_cons_succ, Hn, Hn0_eq, Hn1_eq, Hn2_eq]\n"
        "  simp only [cfK, List.getD_cons_zero, List.getD_cons_succ]\n"
        "  ring\n\n"
        "theorem eK_eq : Cert3K.eK 3 cfK w lam_ = 1 / 2 + 3 * √2 + √3 := by\n"
        "  simp only [Cert3K.eK, Finset.sum_range_succ, Finset.sum_range_zero, w, List.getD_cons_zero,\n"
        "    List.getD_cons_succ, cfK]\n"
        "  have e0 : cf0.eps = eps0_ := rfl\n"
        "  have e1 : cf1.eps = eps1_ := rfl\n"
        "  have e2 : cf2.eps = eps2_ := rfl\n"
        "  rw [e0, e1, e2]\n"
        "  unfold eps0_ eps1_ eps2_ lam_\n"
        "  push_cast\n"
        "  ring\n\n"
        + emit_pos(Fb, Sb) +
        "/-- **The three-point bound for `N = 5`, Coulomb.**  For all unit vectors `x 0, …, x 4` of `ℝ³`,\n"
        "`1/2 + 3√2 + √3 ≤ ∑_{i<j} Hn ⟪x i, x j⟫`. -/\n"
        "theorem bound (x : Fin 5 → R3) (hx : ∀ i, ‖x i‖ = 1) :\n"
        "    (1 / 2 + 3 * √2 + √3 : ℝ) ≤ ∑ i, ∑ j ∈ Finset.Ioi i, Hn ⟪x i, x j⟫ := by\n"
        f"  have h := Cert3K.soundK 3 cfK w 5 lam_ {len(Fb)} {len(Sb)} mF gs σs zs (by norm_num) (by decide +kernel)\n"
        "    hcf hm hsh hF hS x hx\n"
        "  rw [eK_eq] at h\n"
        "  simp only [HK_eq] at h\n"
        "  exact h\n")
    return hd([f"{NS}.Check", f"{NS}.Corner"],
              "N = 5, Coulomb (s = 1): the three-point bound `1/2 + 3√2 + √3 ≤ ∑_{i<j} Hn(⟪x i, x j⟫)` for five unit "
              "vectors of `ℝ³`,\nfrom the checked component certificates `cf0, cf1, cf2` (identities), the checked "
              "`K`-blocks with corner witnesses\n(positivity at `(1, √2, √3)` through the box, `w_aff`) and "
              "`ThomsonN7.Cert.Cert3K.soundK`.  `Hn = Hn0 + √2·Hn1 + √3·Hn2` in the\nmonomial basis.  The "
              "comparison `Hn ≤ φ₁` is not part of this module.") + \
        f"open Real\n\nnamespace {NS}\nopen ThomsonN7 ThomsonN7.Cert ThomsonN7.Cert.Cert3 ThomsonN7.Cert.KB\n\n" + body + \
        f"\nend {NS}\n"


def emit_pos(Fb, Sb):
    K, nS = len(Fb), len(Sb)
    s = ("theorem hcf : ∀ c < 3, (cfK c).n = 5 ∧ (cfK c).Lam = lam_ ∧ (cfK c).an = -1 ∧ (cfK c).ad = 1 ∧\n"
         f"    (cfK c).K = {K} ∧ (cfK c).S.length = {nS} ∧ chk (cfK c).idE = true := by\n"
         "  intro c hc\n"
         "  interval_cases c\n"
         "  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, cf0_chk⟩\n"
         "  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, cf1_chk⟩\n"
         "  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, cf2_chk⟩\n\n"
         f"theorem hm : ∀ c < 3, ∀ k < {K}, (cfK c).m k = mF k := by decide +kernel\n\n"
         f"theorem hsh : ∀ c < 3, ∀ i < {nS}, ((cfK c).S.getD i Cert3K.sDflt).g = gs i ∧\n"
         "    ((cfK c).S.getD i Cert3K.sDflt).σ = σs i ∧ ((cfK c).S.getD i Cert3K.sDflt).z = zs i := by\n"
         "  decide +kernel\n\n")
    for b in Fb:
        k, x = b["idx"], bname(b)
        s += (f"theorem hF{k} : (Cert3K.FmK 3 cfK w lam_ mF {k}).PosSemidef :=\n"
              f"  FmK_psd w_aff {x}_kok (fun c => [F{k}_D0, F{k}_D1, F{k}_D2].getD c [])\n"
              "    (by intro c hc; interval_cases c <;> rfl)\n"
              f"    (by intro c hc; interval_cases c; exacts [F{k}_X0, F{k}_X1, F{k}_X2])\n"
              f"    (by intro c hc; interval_cases c; exacts [F{k}_sym0, F{k}_sym1, F{k}_sym2])\n"
              f"    {x}_mN\n\n")
    s += (f"theorem hF : ∀ k < {K}, (Cert3K.FmK 3 cfK w lam_ mF k).PosSemidef := by\n"
          "  intro k hk\n  interval_cases k\n" + "".join(f"  · exact hF{k}\n" for k in range(K)) + "\n")
    for b in Sb:
        r_, x = b["idx"], bname(b)
        s += (f"theorem hS{r_} (u v t : ℝ) :\n"
              f"    0 ≤ ∑ c ∈ Finset.range 3, w c * (sqfE ((cfK c).S.getD {r_} Cert3K.sDflt).B (zs {r_})).ev u v t :=\n"
              f"  sqf_nonneg w_aff {x}_kok (fun c => ((cfK c).S.getD {r_} Cert3K.sDflt).B)\n"
              "    (by\n"
              "      intro c hc\n"
              "      interval_cases c\n"
              f"      · exact congrArg (fun X => (⟨[], [], X⟩ : Blk)) S{r_}_X0\n"
              f"      · exact congrArg (fun X => (⟨[], [], X⟩ : Blk)) S{r_}_X1\n"
              f"      · exact congrArg (fun X => (⟨[], [], X⟩ : Blk)) S{r_}_X2)\n"
              f"    (zs {r_}) (by decide +kernel) u v t\n\n")
    s += (f"theorem hS : ∀ i < {nS}, ∀ u v t : ℝ,\n"
          "    0 ≤ ∑ c ∈ Finset.range 3, w c * (sqfE ((cfK c).S.getD i Cert3K.sDflt).B (zs i)).ev u v t := by\n"
          "  intro i hi\n  interval_cases i\n" + "".join(f"  · exact hS{r_}\n" for r_ in range(nS)) + "\n")
    return s


# ====================================================================== --check: parse the emitted files
HEX = r"(0x[0-9a-f]+|\d+)"


def _num(s): return int(s, 16) if s.startswith("0x") else int(s)


def parse_mat(s):
    s = s.strip()
    assert s.startswith("[[") or s == "[]", s[:40]
    return [[int(v) for v in row.split(",") if v.strip()] for row in re.findall(r"\[([-0-9, ]*)\]", s[1:-1])]


def parse_defs(txt):
    """name -> value for `def name : List (List Int|ℤ) := ...`, `List Int|ℤ`, Blk/SBlk/κ literals."""
    v = {}
    for mt in re.finditer(r"def (\S+) : List \(List (?:Int|ℤ)\) := unpackM (\d+) (\d+) (\d+)\s+" + HEX, txt):
        v[mt.group(1)] = E5.unpackM(int(mt.group(2)), int(mt.group(3)), int(mt.group(4)), _num(mt.group(5)))
    for mt in re.finditer(r"def (\S+) : List \(List (?:Int|ℤ)\) := (\[\[.*?\]\])\n", txt, re.S):
        v[mt.group(1)] = parse_mat(mt.group(2))
    for mt in re.finditer(r"def (\S+) : List (?:Int|ℤ) := unpackI (\d+) (\d+)\s+" + HEX, txt):
        v[mt.group(1)] = E5.unpackI(int(mt.group(2)), int(mt.group(3)), _num(mt.group(4)))
    for mt in re.finditer(r"def (\S+) : List (?:Int|ℤ) := \[([-0-9, ]*)\]\n", txt):
        v[mt.group(1)] = [int(x) for x in mt.group(2).split(",") if x.strip()]
    for mt in re.finditer(r"def (\S+) : List \(List \(List ℤ\)\) := \[([A-Za-z0-9_, ]*)\]", txt):
        v[mt.group(1)] = [v[x.strip()] for x in mt.group(2).split(",")]
    for mt in re.finditer(r"def (\S+) : List \(List ℤ\) := \[(κ[0-9, κ]*)\]", txt):
        v[mt.group(1)] = [v[x.strip()] for x in mt.group(2).split(",")]
    for mt in re.finditer(r"def (\S+) : Blk := ⟨(\S+), (\S+), (\S+)⟩", txt):
        a, b, c = mt.group(2, 3, 4)
        v[mt.group(1)] = ("Blk", [] if a == "[]" else v[a], [] if b == "[]" else v[b], v[c])
    for mt in re.finditer(r"def (\S+) : List \(Nat × Nat × Nat\) := (\[.*?\])\n", txt):
        v[mt.group(1)] = [tuple(int(y) for y in t.split(",")) for t in re.findall(r"\(([0-9, ]+)\)", mt.group(2))]
    for mt in re.finditer(r"def (\S+) : SBlk := ⟨\[([0-9, ]*)\], (\d+), (\S+), ⟨\[\], \[\], (\S+)⟩⟩", txt):
        v[mt.group(1)] = ("SBlk", [int(x) for x in mt.group(2).split(",") if x.strip()], int(mt.group(3)),
                          v[mt.group(4).rstrip(",")], v[mt.group(5)])
    return v


def parse(outdir):
    rd = lambda f: open(os.path.join(outdir, f), encoding="utf-8").read()
    dt, bt = rd("Data.lean"), rd("Blocks.lean")
    V = parse_defs(dt)
    V.update(parse_defs(bt))
    for mt in re.finditer(r"def (F\d+_D\d) : List \(List Int\) := (\[\[.*?\]\])\n", dt):
        V[mt.group(1)] = parse_mat(mt.group(2))
    data = dict(Lam=int(re.search(r"def lam_ : Nat := (\d+)", dt).group(1)))
    data["h"] = [V[f"h{c}_"] for c in range(Q)]
    data["eps"] = [int(re.search(rf"def eps{c}_ : Int := \((-?\d+) : Int\)", dt).group(1)) for c in range(Q)]
    cfs = []
    for c in range(Q):
        mt = re.search(rf"def cf{c} : Cert3 :=\s+\{{ n := (\d+), Lam := lam_, an := (-?\d+), ad := (\d+), "
                       rf"h := h{c}_, eps := eps{c}_,\s+F := \[([A-Za-z0-9_, ]*)\],\s+S := \[([A-Za-z0-9_, ]*)\] \}}", dt)
        n, an, ad = int(mt.group(1)), int(mt.group(2)), int(mt.group(3))
        F = [E5.Blk([], [], V[f.strip()][3]) for f in mt.group(4).split(",")]
        S = []
        for sn in mt.group(5).split(","):
            _, g, sig, z, X = V[sn.strip()]
            S.append(E5.SBlk(g, sig, z, E5.Blk([], [], X)))
        cfs.append(E5.Cert3(n, data["Lam"], an, ad, data["h"][c], data["eps"][c], F, S))
    data["cfs"] = cfs
    data["kap"] = V["κs"]
    data["V"] = V
    stats, wD = {}, {}
    for c in range(Q):
        t = rd(f"ChkI{c}.lean")
        for mt in re.finditer(r"def stat(\S+)_(\d) : ThomsonN7\.Case1\.C1Stat :=\s+\((\d+), (\d+), (\d+), (\d+), "
                              r"\((-?)(0x[0-9a-f]+) : Int\)\)", t):
            kv = int(mt.group(8), 16) * (-1 if mt.group(7) else 1)
            stats[(int(mt.group(2)), mt.group(1))] = (int(mt.group(3)), int(mt.group(4)), int(mt.group(5)),
                                                      int(mt.group(6)), kv)
        wD[c] = set((int(a), int(b)) for a, b in re.findall(r"ThomsonN7\.Case1\.c1Stat (\d+) (\d+) ", t))
    data["stats"], data["wD"] = stats, wD
    data["check"] = rd("Check.lean")
    data["bound"] = rd("Bound.lean")
    data["chkF"] = rd("ChkF.lean")
    return data


def check_emitted(outdir, J=None):
    P = parse(outdir)
    V, ok = P["V"], True
    L_ = P["Lam"]
    log(f"parsed: Λ = {L_} ({L_.bit_length()} bits), corners {P['kap']}")
    # identities
    for c, cf in enumerate(P["cfs"]):
        g = cf.n == 5 and cf.an == -1 and cf.ad == 1 and cf.Lam == L_ and cf.K == 4 and len(cf.S) == 8
        pcs = E5.pieces(cf)
        lst = {nm: E5.stat_l(e) for nm, e in pcs}
        z0 = lambda nm: lst[nm] + (0,)
        tot0 = E5.compose_idE(cf, z0("H"), [z0(f"F{k}") for k in range(cf.K)], [z0(f"S{i}") for i in range(len(cf.S))])
        w, D = E5.chk_params(*tot0[:4])
        st = {nm: lst[nm] + (E5.kev(e, w, D),) for nm, e in pcs}
        tot = E5.compose_idE(cf, st["H"], [st[f"F{k}"] for k in range(cf.K)], [st[f"S{i}"] for i in range(len(cf.S))])
        g &= P["wD"][c] == {(w, D)}
        g &= all(P["stats"].get((c, nm)) == s for nm, s in st.items())
        g &= tot[4] == 0 and E5.chk_params(*tot[:4]) == (w, D)
        g &= (f"c1Stat {w} {D} cf{c}.idE = ({tot[0]}, {tot[1]}, {tot[2]}, {tot[3]}, (0 : Int))" in P["check"]
              and f"Nat.log2 {tot[0]} + 1 = {w}" in P["check"])
        log(f"component {c}: structure, (w, D) = ({w}, {D}), 13 piece statistics, composition kev = {tot[4]}: "
            f"{'OK' if g else 'FAILED'}")
        ok &= g
    # blocks
    for kind, n_ in (("F", 4), ("S", 8)):
        for i in range(n_):
            x = f"n{kind}{i}"
            N, Es, d, l, Pm = V[f"{x}_N"], V[f"{x}_Es"], V[f"{x}_d"], V[f"{x}_l"], V[f"{x}_P"]
            r = len(d)
            Xs = [V[f"{kind}{i}_D{c}"] for c in range(Q)]
            m = len(Xs[0])
            p = dict(X=all(Xs[c] == expandE(N, Es[c]) for c in range(Q)), mN=m <= len(N),
                     hN=all(len(row) <= r for row in N), hE=all(len(E) <= r and all(len(rw) <= r for rw in E) for E in Es),
                     hq=len(Es) <= Q, P=E5.ldl(d, l) == Pm and len(Pm) == r)
            if kind == "F":
                p["sym"] = all([row[:m] for row in X] == E5.transposeSq(m, X) for X in Xs)
            cs = []
            for j, k in enumerate(P["kap"]):
                _, dj, lj, Rj = V[f"{x}_C{j}"]
                cs.append(dj == d and lj == l and len(k) <= Q and okF(r, dj, lj, Rj) and len(dj) <= r and len(lj) <= r
                          and E5.matAdd(Pm, Rj) == lin(k, Es))
            p["corners"] = all(cs)
            g = all(p.values())
            ok &= g
            log(f"block {kind}{i} ({m} × {r}): {'OK' if g else p}")
    # Bound.lean literals: Hn coefficients and the box
    B = P["bound"]
    hn_ok = True
    for c in range(Q):
        blk = re.search(rf"noncomputable def Hn{c} \(x : ℝ\) : ℝ :=(.*?)\n\n", B, re.S).group(1)
        co = [Fr(int(a), int(b) if b else 1) for a, b in re.findall(r"\((-?\d+)(?: / (\d+))? : ℝ\)", blk)]
        hn_ok &= co == [Fr(x, L_) for x in P["h"][c]]
    log(f"Bound.lean: Hn0..Hn2 coefficients = h_c / Λ: {hn_ok}")
    ok &= hn_ok
    if J is not None:
        bits = (P["kap"][0][0]).bit_length() - 1
        data = build_from_parsed(P, bits)
        cc = json_crosscheck(data, J)
        log(f"JSON cross-check (exact, per component; box contains (√2, √3)): {cc}")
        ok &= all(cc.values())
    sizes = {fn: os.path.getsize(os.path.join(outdir, fn)) for fn in sorted(os.listdir(outdir)) if fn.endswith(".lean")}
    log(f"module sizes (bytes): {sizes}")
    log("CHECK " + ("ALL_OK" if ok else "FAILED"))
    return ok


def build_from_parsed(P, bits):
    V = P["V"]
    blocks = []
    for kind, n_ in (("F", 4), ("S", 8)):
        for i in range(n_):
            blocks.append(dict(kind=kind, idx=i, X=[V[f"{kind}{i}_D{c}"] for c in range(Q)]))
    cf0 = P["cfs"][0]
    return dict(Lam=P["Lam"], h=P["h"], eps=P["eps"], blocks=blocks, bits=bits, kap=P["kap"],
                codes=[s.g for s in cf0.S], z=[s.z for s in cf0.S])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json", nargs="?")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--json", dest="json2")
    ap.add_argument("--outdir", default=DEF_OUT)
    ap.add_argument("--bits", type=int, default=32)
    a = ap.parse_args()
    if a.check:
        jp = a.json2 or a.json
        sys.exit(0 if check_emitted(a.outdir, json.load(open(jp)) if jp else None) else 1)
    raw = open(a.json, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    J = json.loads(raw)
    data = build(J, a.bits)
    rep = simulate(data)
    log(f"simulation: ok = {rep['ok']}")
    if not rep["ok"]:
        raise SystemExit("simulated Lean checks FAILED; nothing emitted")
    cc = json_crosscheck(data, J)
    log(f"JSON cross-check: {cc}")
    if not all(cc.values()):
        raise SystemExit("integer data differ from the JSON; nothing emitted")
    files = emit(data, rep, os.path.basename(a.json), sha, a.outdir)
    for nm, txt in files.items():
        log(f"  wrote {os.path.join(a.outdir, nm)} ({len(txt.encode())} bytes)")
    sys.exit(0 if check_emitted(a.outdir, J) else 1)


if __name__ == "__main__":
    main()
