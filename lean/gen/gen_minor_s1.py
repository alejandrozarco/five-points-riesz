#!/usr/bin/env python3
"""Generate N5R1Minor/Minor.lean: for the H of cert_n5_s1_short.json (N = 5, Coulomb s = 1, coefficients in
K = Q(sqrt2, sqrt3)), H > 0 on [-1, 1] and H <= phi1(t) = 1/sqrt(2-2t) on [-1, 1), equality exactly at -1, -1/2, 0.

usage: python3 gen_minor_s1.py cert_n5_s1_short.json OUT.lean

Proof shape (all numbers exact rationals; s2, s3, s6 stand for sqrt2, sqrt3, sqrt6):
  * Hm(t) = Hm0(t) + s2 Hm1(t) + s3 Hm2(t)  (monomial form; the sqrt6-component of H is 0);
  * qm(t) = qm0(t) + s2 qm1(t) + s3 qm2(t) + s6 qm3(t) with, component by component (rational identities, `ring`),
      1 - (2-2t)(Hm0^2 + 2 Hm1^2 + 3 Hm2^2) = D(t) qm0,   -(2-2t) 2 Hm0 Hm1 = D(t) qm1,
      -(2-2t) 2 Hm0 Hm2 = D(t) qm2,                        -(2-2t) 2 Hm1 Hm2 = D(t) qm3,     D(t) = (t+1)(2t+1)^2 t^2;
    together with s2^2 = 2, s3^2 = 3, s2 s3 = s6 this gives 1 - (2-2t) Hm^2 = D(t) qm (`linear_combination`);
  * positivity of P in {Hm, qm} on each interval [a, b] of a cover of [-1, 1]: the Bernstein identity
      P(t) - delta = sum_i (beta_i(s) - delta) C(n,i) x^i y^(n-i),  x = (t-a)/(b-a), y = (b-t)/(b-a)   (`ring`),
    where beta_i(s) is affine in (s2, s3, s6) with rational coefficients; each beta_i(s) - delta >= 0 follows by
    `linarith` from rational bounds lo <= s <= hi (lo^2 <= m <= hi^2, box width 2^-BITS).
"""
import json, sys, math
from fractions import Fraction as Fr
from flint import fmpq_poly, fmpq

BITS = 64
HB = 4000000   # heartbeat budget for the large `ring` identities
cert = json.load(open(sys.argv[1])); out = sys.argv[2]

def F(x): return Fr(x)
def fq(x): return fmpq(x.numerator, x.denominator)
def toFr(p, n=None):
    c = [Fr(int(x.p), int(x.q)) for x in p.coeffs()]
    if n is not None: c += [Fr(0)] * (n + 1 - len(c))
    return c
def P(cs): return fmpq_poly([fq(c) for c in cs])

# --- H in monomial form, per component
D = cert["D"]; Hch = [[F(x) for x in z] for z in cert["H_chebyshev"]]; assert len(Hch) == D + 1
t = fmpq_poly([0, 1]); T = [fmpq_poly([1]), t]
while len(T) <= D: T.append(2 * t * T[-1] - T[-2])
Hc = [sum((T[j] * fq(Hch[j][c]) for j in range(D + 1)), fmpq_poly([])) for c in range(4)]
assert Hc[3] == 0, "sqrt6-component of H must vanish"
H0, H1, H2 = Hc[:3]
den = fmpq_poly([1, 1]) * fmpq_poly([1, 2]) ** 2 * t ** 2
one_m = fmpq_poly([2, -2])
comp = [1 - one_m * (H0 * H0 + 2 * H1 * H1 + 3 * H2 * H2), -one_m * 2 * H0 * H1, -one_m * 2 * H0 * H2, -one_m * 2 * H1 * H2]
qc = []
for c in comp:
    qq, rr = divmod(c, den); assert rr == 0, "D(t) does not divide a component"; qc.append(qq)
import os
nq = max(q.degree() for q in qc); nH = max(h.degree() for h in Hc)

# --- box around (sqrt2, sqrt3, sqrt6)
box = {}
for m in (2, 3, 6):
    lo = Fr(math.isqrt(m << (2 * BITS)), 1 << BITS); hi = lo + Fr(1, 1 << BITS)
    assert 0 < lo and lo * lo <= m <= hi * hi and lo * lo != m; box[m] = (lo, hi)

def bern(cs, n, a, b):
    g = P(cs)(fmpq_poly([fq(a), fq(b - a)])); c = toFr(g, n)
    return [sum(Fr(math.comb(i, j), math.comb(n, j)) * c[j] for j in range(i + 1)) for i in range(n + 1)]
def boxmin(beta):   # minimum over the box of beta[0] + beta[1] s2 + beta[2] s3 + beta[3] s6
    return beta[0] + sum(min(beta[k] * box[m][0], beta[k] * box[m][1]) for k, m in ((1, 2), (2, 3), (3, 6)))

def certify(comps, n, intervals, name):
    cs = [toFr(c, n) for c in comps]; cs += [[Fr(0)] * (n + 1)] * (4 - len(cs))
    res = []; worst = None
    for a, b in intervals:
        betas = list(zip(*[bern(cs[k], n, a, b) for k in range(4)]))
        mn = min(boxmin(be) for be in betas); worst = mn if worst is None else min(worst, mn)
        res.append(betas)
    assert worst > 0, f"{name}: Bernstein minimum over the box {float(worst)} <= 0"
    delta = Fr(1, 1 << (1 - math.floor(math.log2(worst))))   # power of 2 with delta <= worst / 2
    assert 0 < delta <= worst / 2
    print(f"{name}: degree {n}, intervals {[(str(a), str(b)) for a, b in intervals]}, min Bernstein coefficient over "
          f"box {float(worst):.4e}, delta = 2^{-int(math.log2(1 / delta))}")
    return res, delta

def try_cover(comps, n, name, covers):
    for cov in covers:
        try: return cov, certify(comps, n, cov, name)
        except AssertionError as e: print("  cover", [(str(a), str(b)) for a, b in cov], "fails:", e)
    raise SystemExit(f"{name}: no cover works")
h = Fr(1, 2)
covers = [[(Fr(-1), Fr(1))], [(Fr(-1), Fr(0)), (Fr(0), Fr(1))], [(Fr(-1), Fr(0)), (Fr(0), h), (h, Fr(1))],
          [(Fr(-1), -h), (-h, Fr(0)), (Fr(0), h), (h, Fr(1))]]
Hcov, (Hbeta, Hdelta) = try_cover([H0, H1, H2], nH, "H", covers)
qcov, (qbeta, qdelta) = try_cover(qc, nq, "q", covers)

# --- Lean text
def lit(v):
    v = Fr(v)
    return f"({v.numerator} : ℝ)" if v.denominator == 1 else f"(({v.numerator} : ℝ) / {v.denominator})"
def poly(p, var="t"):
    cs = toFr(p); s = " + ".join(f"{lit(c)} * {var} ^ {k}" for k, c in enumerate(cs) if c != 0)
    return s if s else "0"
SN = {1: "√2", 2: "√3", 3: "√6"}
def kexpr(be):   # affine expression in √2, √3, √6
    parts = [lit(be[0])] + [f"{lit(be[k])} * {SN[k]}" for k in (1, 2, 3) if be[k] != 0]
    return "(" + " + ".join(parts) + ")"
def xy(a, b):
    w = b - a
    xa = f"(t - {lit(a)})" if a != 0 else "t"
    yb = f"({lit(b)} - t)" if b != 0 else "(-t)"
    return (f"({xa} / {lit(w)})", f"({yb} / {lit(w)})") if w != 1 else (xa, yb)
def bern_lean(betas, n, a, b, delta):
    x, y = xy(a, b); terms = []
    for i, be in enumerate(betas):
        be2 = [be[0] - delta, be[1], be[2], be[3]]; be2 = [v * math.comb(n, i) for v in be2]
        terms.append(f"{kexpr(be2)} * {x} ^ {i} * {y} ^ {n - i}")
    return terms
def nonneg_term(nterms, n):
    # (((T0 + T1) + T2) + ...), Ti = c_i * x^i * y^(n-i)
    tm = lambda i: f"(mul_nonneg (mul_nonneg hb{i} (pow_nonneg hx {i})) (pow_nonneg hy {n - i}))"
    e = tm(0)
    for i in range(1, nterms): e = f"(add_nonneg {e} {tm(i)})"
    return e
def pos_block(fname, unfold, n, cov, betas, delta, tag):
    lines = []
    for j, ((a, b), be) in enumerate(zip(cov, betas)):
        terms = bern_lean(be, n, a, b, delta)
        x, y = xy(a, b)
        lines.append(f"""set_option maxHeartbeats {HB} in
/-- Bernstein form of `{fname} - {delta}` on `[{a}, {b}]` (identity in `t`, `√2`, `√3`, `√6`). -/
theorem {tag}_bern{j} (t : ℝ) : {fname} t - {lit(delta)} =
    {(" +" + chr(10) + "    ").join(terms)} := by
  unfold {unfold}; ring

theorem {tag}_pos{j} {{t : ℝ}} (h1 : {lit(a)} ≤ t) (h2 : t ≤ {lit(b)}) : {lit(delta)} ≤ {fname} t := by
  obtain ⟨l2, u2, l3, u3, l6, u6⟩ := minor_box
  have hx : 0 ≤ {x} := by {"positivity" if False else "apply div_nonneg <;> linarith" if (b - a) != 1 else "linarith"}
  have hy : 0 ≤ {y} := by {"apply div_nonneg <;> linarith" if (b - a) != 1 else "linarith"}
""")
        for i in range(n + 1):
            be2 = [(be[i][0] - delta) * math.comb(n, i), be[i][1] * math.comb(n, i), be[i][2] * math.comb(n, i),
                   be[i][3] * math.comb(n, i)]
            lines.append(f"  have hb{i} : 0 ≤ {kexpr(be2)} := by linarith\n")
        lines.append(f"  have := {tag}_bern{j} t\n  have : 0 ≤ {fname} t - {lit(delta)} := by\n"
                     f"    rw [this]; exact {nonneg_term(n + 1, n)}\n  linarith\n\n")
    # combine intervals
    comb = [f"theorem {tag}_ge {{t : ℝ}} (h1 : -1 ≤ t) (h2 : t ≤ 1) : {lit(delta)} ≤ {fname} t := by\n"]
    def split(k):
        if k == len(cov) - 1:
            return f"exact {tag}_pos{k} (by linarith) (by linarith)"
        b = cov[k][1]
        return (f"rcases le_total t {lit(b)} with h | h\n" + "  " * (k + 1) + f"· exact {tag}_pos{k} (by linarith) h\n"
                + "  " * (k + 1) + "· " + split(k + 1))
    comb.append("  " + split(0) + "\n\n")
    return "".join(lines) + "".join(comb)

b2, b3, b6 = box[2], box[3], box[6]
Hdef = f"Hm0 t + √2 * Hm1 t + √3 * Hm2 t"
lean = f'''import Mathlib

/-!
# N = 5, Coulomb (s = 1): the one-dimensional minorant `H ≤ φ₁` on `[-1, 1)`

`Hm` is the degree-10 polynomial `H` of the three-point certificate (`cert_n5_s1_short.json`), with coefficients in
`ℚ(√2, √3)`, in monomial form: `Hm t = Hm0 t + √2 * Hm1 t + √3 * Hm2 t` with rational polynomials `Hm0, Hm1, Hm2`.
With `φ₁(t) = 1/√(2-2t)` and `D(t) = (t+1)(2t+1)² t²`:
* `1 - (2-2t) Hm(t)² = D(t) qm(t)` with `qm = qm0 + √2 qm1 + √3 qm2 + √6 qm3` (`minor_factor`): four rational
  identities, one per component of `ℚ(√2, √3)` (`ring`), combined using `√2² = 2`, `√3² = 3`, `√2 √3 = √6`;
* positivity of `Hm` and `qm` on `[-1, 1]` (`Hm_ge`, `qm_ge`): on each interval of a cover of `[-1, 1]`, a Bernstein
  identity `P(t) - δ = Σ βᵢ C(n,i) xⁱ yⁿ⁻ⁱ` (`ring`, with `√2, √3, √6` as atoms), where each `βᵢ` is affine in
  `(√2, √3, √6)` with rational coefficients and is `≥ 0` by `linarith` from rational bounds on `√2, √3, √6`
  (box of width `2^-{BITS}`, `minor_box`).

Hence `Hm > 0` on `[-1, 1]` (`H_pos`), `Hm ≤ φ₁` on `[-1, 1)` (`H_le`), with equality exactly at `t ∈ {{-1, -1/2, 0}}`
(`H_eq_iff`). Generated by `lean/gen/gen_minor_s1.py`.  Regenerate; do not edit.
-/

namespace N5R1

/-- Rational component of `H`. -/
noncomputable def Hm0 (t : ℝ) : ℝ :=
  {poly(H0)}

/-- `√2`-component of `H`. -/
noncomputable def Hm1 (t : ℝ) : ℝ :=
  {poly(H1)}

/-- `√3`-component of `H`. -/
noncomputable def Hm2 (t : ℝ) : ℝ :=
  {poly(H2)}

/-- The polynomial `H` of the certificate (the `√6`-component of every coefficient is `0`). -/
noncomputable def Hm (t : ℝ) : ℝ := {Hdef}

noncomputable def qm0 (t : ℝ) : ℝ :=
  {poly(qc[0])}

noncomputable def qm1 (t : ℝ) : ℝ :=
  {poly(qc[1])}

noncomputable def qm2 (t : ℝ) : ℝ :=
  {poly(qc[2])}

noncomputable def qm3 (t : ℝ) : ℝ :=
  {poly(qc[3])}

/-- The cofactor `q` with `1 - (2-2t) H² = (t+1)(2t+1)² t² q`. -/
noncomputable def qm (t : ℝ) : ℝ := qm0 t + √2 * qm1 t + √3 * qm2 t + √6 * qm3 t

set_option maxHeartbeats {HB} in
theorem minor_factor0 (t : ℝ) :
    1 - (2 - 2 * t) * (Hm0 t ^ 2 + 2 * Hm1 t ^ 2 + 3 * Hm2 t ^ 2) = (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm0 t := by
  unfold Hm0 Hm1 Hm2 qm0; ring

set_option maxHeartbeats {HB} in
theorem minor_factor1 (t : ℝ) : -(2 - 2 * t) * (2 * Hm0 t * Hm1 t) = (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm1 t := by
  unfold Hm0 Hm1 qm1; ring

set_option maxHeartbeats {HB} in
theorem minor_factor2 (t : ℝ) : -(2 - 2 * t) * (2 * Hm0 t * Hm2 t) = (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm2 t := by
  unfold Hm0 Hm2 qm2; ring

set_option maxHeartbeats {HB} in
theorem minor_factor3 (t : ℝ) : -(2 - 2 * t) * (2 * Hm1 t * Hm2 t) = (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm3 t := by
  unfold Hm1 Hm2 qm3; ring

theorem minor_sqrt6 : √6 = √2 * √3 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- `1 - (2-2t) H² = (t+1)(2t+1)² t² q` over `ℝ`. -/
theorem minor_factor (t : ℝ) : 1 - (2 - 2 * t) * Hm t ^ 2 = (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm t := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 := minor_sqrt6
  unfold Hm qm
  linear_combination minor_factor0 t + √2 * minor_factor1 t + √3 * minor_factor2 t + √6 * minor_factor3 t
    - (2 - 2 * t) * Hm1 t ^ 2 * h2 - (2 - 2 * t) * Hm2 t ^ 2 * h3 + 2 * (2 - 2 * t) * Hm1 t * Hm2 t * h6

/-- Rational bounds on `√2`, `√3`, `√6` (width `2^-{BITS}`). -/
theorem minor_box : {lit(b2[0])} ≤ √2 ∧ √2 ≤ {lit(b2[1])} ∧ {lit(b3[0])} ≤ √3 ∧ √3 ≤ {lit(b3[1])} ∧
    {lit(b6[0])} ≤ √6 ∧ √6 ≤ {lit(b6[1])} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt' (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num
  · rw [Real.le_sqrt' (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num
  · rw [Real.le_sqrt' (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

{pos_block("Hm", "Hm Hm0 Hm1 Hm2", nH, Hcov, Hbeta, Hdelta, "Hm")}{pos_block("qm", "qm qm0 qm1 qm2 qm3", nq, qcov, qbeta, qdelta, "qm")}/-- **`H > 0` on `[-1, 1]`.** -/
theorem H_pos {{t : ℝ}} (h1 : -1 ≤ t) (h2 : t ≤ 1) : 0 < Hm t :=
  lt_of_lt_of_le (by norm_num) (Hm_ge h1 h2)

theorem qm_pos {{t : ℝ}} (h1 : -1 ≤ t) (h2 : t ≤ 1) : 0 < qm t :=
  lt_of_lt_of_le (by norm_num) (qm_ge h1 h2)

/-- `(2 - 2t) H² ≤ 1` on `[-1, 1]`, with equality iff `D(t) q(t) = 0`. -/
theorem minor_sq_le {{t : ℝ}} (h1 : -1 ≤ t) (h2 : t ≤ 1) : (2 - 2 * t) * Hm t ^ 2 ≤ 1 := by
  have hf := minor_factor t
  have hq := qm_pos h1 h2
  have : 0 ≤ (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm t := by
    have : 0 ≤ t + 1 := by linarith
    positivity
  linarith

/-- **`H ≤ φ₁` on `[-1, 1)`.** -/
theorem H_le {{t : ℝ}} (h1 : -1 ≤ t) (h2 : t < 1) : Hm t ≤ 1 / √(2 - 2 * t) := by
  have hd : 0 < 2 - 2 * t := by linarith
  have hs : 0 < √(2 - 2 * t) := Real.sqrt_pos.2 hd
  rw [le_div_iff₀ hs]
  have hx : 0 ≤ Hm t * √(2 - 2 * t) := mul_nonneg (H_pos h1 h2.le).le hs.le
  have hsq : (Hm t * √(2 - 2 * t)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hd.le]; nlinarith [minor_sq_le h1 h2.le]
  nlinarith

/-- Equality holds exactly at the inner products of the triangular bipyramid. -/
theorem H_eq_iff {{t : ℝ}} (h1 : -1 ≤ t) (h2 : t < 1) :
    Hm t = 1 / √(2 - 2 * t) ↔ t = -1 ∨ t = -1 / 2 ∨ t = 0 := by
  have hd : 0 < 2 - 2 * t := by linarith
  have hs : 0 < √(2 - 2 * t) := Real.sqrt_pos.2 hd
  have hss : √(2 - 2 * t) ^ 2 = 2 - 2 * t := Real.sq_sqrt hd.le
  have hq := qm_pos h1 h2.le
  have hf := minor_factor t
  have hH := H_pos h1 h2.le
  constructor
  · intro h
    have h1' : Hm t * √(2 - 2 * t) = 1 := by rw [h, one_div_mul_cancel hs.ne']
    have h0 : (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm t = 0 := by
      rw [← hf, ← hss]; linear_combination (-(Hm t * √(2 - 2 * t)) - 1) * h1'
    rcases mul_eq_zero.1 h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · rcases mul_eq_zero.1 h0 with h0 | h0
        · left; linarith
        · right; left; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0; linarith
      · right; right; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    · exact absurd h0 hq.ne'
  · intro h
    have h0 : (t + 1) * (2 * t + 1) ^ 2 * t ^ 2 * qm t = 0 := by
      rcases h with h | h | h <;> subst h <;> ring
    rw [← hf, ← hss] at h0
    have hx : 0 ≤ Hm t * √(2 - 2 * t) := mul_nonneg hH.le hs.le
    have hx1 : Hm t * √(2 - 2 * t) = 1 := by nlinarith
    rw [eq_div_iff hs.ne']
    exact hx1

end N5R1
'''
open(out, 'w').write(lean)
bits = max(max(abs(v.numerator).bit_length(), v.denominator.bit_length()) for p in (H0, H1, H2) for v in toFr(p))
print("wrote", out, f"({len(lean)} bytes); H coefficient max bits: {bits}")
