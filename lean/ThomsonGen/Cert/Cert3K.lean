import ThomsonGen.Cert.Cert3N

/-!
# Three-point certificates over a real number field (`Cert3K`)

A certificate whose numbers lie in a field `K = ℚ(θ₁, …)` with a `ℚ`-basis `1 = θ₀, θ₁, …, θ_{q-1}`
(for the Coulomb certificate of five points: `K = ℚ(√2, √3)` with basis `1, √2, √3, √6`; the coefficients are
supported on `1, √2, √3`, the `√6`-components being zero) is split into `q` rational component certificates `cf c : Cert3` (`c < q`).  The structure of the
certificate (the number of points `n`, the kernel block sizes, the SOS multipliers, permutations and monomial
bases) is rational and shared; the identity of the certificate is `K`-linear in its numerical data, so its
`c`-component is the identity of `cf c`, checked by upstream's `chk (cf c).idE`.  The `w`-weighted sum of the
component identities (`w c = θ_c` as real numbers) is the real identity with

* `H_K(x) = ∑_c w_c · H_c(x)`, `e_K = ∑_c w_c · e_c` (`HK`, `eK`),
* kernel matrices `F_K = ∑_c w_c · F_c` (`FmK`) and SOS Gram matrices `B_K = ∑_c w_c · B_c`.

The component blocks are not positive semidefinite; positivity is needed only for the `w`-weighted sums.  For
a fixed vector `y`, `yᵀ B_K y = ∑_c w_c (yᵀ B_c y)` is linear in `w`; if `w` lies in the convex hull of
a finite set of (scaled) rational corners `κ` (`AffOK`: every linear functional nonnegative at the corners is
nonnegative at `w`), it suffices that `∑_c κ_c B_c` be positive semidefinite at every corner.  These corner
blocks are rational and are certified by upstream's fast check `okF` (`LDLᵀ` with nonnegative pivots plus a
diagonally dominant remainder); facially reduced blocks `N · B′ · Nᵀ` are handled by congruence as in
`NBlk.lean` (`expandE`, `qf_expandE`).

* `KB.lin`, `KB.getD_lin`, `KB.qf_lin`: list-matrix linear combinations `∑_c κ_c M_c`;
* `KB.KOK`: a checked `K`-block (basis `N`, component reduced blocks `Ms`, corner witnesses `bs`);
  `KB.KOK.qf_nonneg`: `0 ≤ ∑_c w_c · yᵀ M_c y` for every `y`, given `AffOK q w κs`;
* `KB.FmK_psd`, `KB.sqf_nonneg`: the kernel / SOS positivity inputs of the soundness theorem;
* `Cert3K.soundK`: `e_K ≤ ∑_{i<j} H_K(⟪x i, x j⟫)` for all unit vectors `x : Fin n → R3`.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `Cert.Cert3K.final_eq` ← `Cert.final_ineq` (equality version);
* `Cert.Cert3K.comp_eq` ← `Cert.Cert3.hpt_gramCut` (evaluation of the identity, as an equation);
* `Cert.Cert3K.sos_comb_nonneg` ← `Cert.sos_sum_nonneg` and `Cert.sblkE_nonneg`;
* `Cert.Cert3K.soundK` ← `Cert.Cert3.sound` (with `Cert.Cert3.hpt`);
* `Cert.KB.qf_lin` ← three lines of `ThreePoint.dsum_pair12`; `Cert.KB.qf_expandE` ← three lines of `Cert.ev_fpE`;
* `Cert.KB.FmK_psd` ← `Cert.fmat_psd`; `Cert.KB.getD_lin` ← `Cert.NBlk.getD_ldl` (ours, itself list arithmetic
  in the style of upstream).
-/

open Real

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert
open ThreePoint
open scoped RealInnerProductSpace

namespace KB

/-! ## List-matrix linear combinations -/

/-- `a · M`. -/
def matScale (a : ℤ) (M : List (List ℤ)) : List (List ℤ) := M.map (NBlk.pscale a)

/-- `∑_c κ_c · M_c` (zip-truncating). -/
def lin : List ℤ → List (List (List ℤ)) → List (List ℤ)
  | a :: as, M :: Ms => NBlk.matAdd (matScale a M) (lin as Ms)
  | _, _ => []

lemma getD_matScale (a : ℤ) (M : List (List ℤ)) (i j : ℕ) :
    ((matScale a M).getD i []).getD j 0 = a * (M.getD i []).getD j 0 := by
  rw [matScale, getD_map_list (NBlk.pscale a) rfl, NBlk.getD_pscale]

lemma getD_lin (q : ℕ) : ∀ (κ : List ℤ) (Ms : List (List (List ℤ))), κ.length ≤ q → Ms.length ≤ q →
    ∀ i j, ((lin κ Ms).getD i []).getD j 0
      = ∑ c ∈ Finset.range q, κ.getD c 0 * ((Ms.getD c []).getD i []).getD j 0 := by
  induction q with
  | zero =>
    intro κ Ms hκ _ i j
    have : κ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [lin]
  | succ q ih =>
    intro κ Ms hκ hM i j
    rw [Finset.sum_range_succ']
    cases κ with
    | nil => simp [lin]
    | cons a as =>
      cases Ms with
      | nil => simp [lin]
      | cons M Ms =>
        simp only [lin, NBlk.getD_matAdd, getD_matScale, List.getD_cons_succ, List.getD_cons_zero]
        rw [ih as Ms (by simp at hκ; omega) (by simp at hM; omega) i j]
        ring

/-! ## Quadratic forms of list matrices -/

/-- `yᵀ E y` over the indices `< r`. -/
noncomputable def qf (r : ℕ) (E : List (List ℤ)) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, y i * (((E.getD i []).getD j 0 : ℤ) : ℝ) * y j

lemma sum3_comm' (s t u : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma qf_lin (r q : ℕ) (κ : List ℤ) (Ms : List (List (List ℤ))) (hκ : κ.length ≤ q)
    (hM : Ms.length ≤ q) (y : ℕ → ℝ) :
    qf r (lin κ Ms) y = ∑ c ∈ Finset.range q, (κ.getD c 0 : ℝ) * qf r (Ms.getD c []) y := by
  unfold qf
  calc ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
          y i * ((((lin κ Ms).getD i []).getD j 0 : ℤ) : ℝ) * y j
      = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, ∑ c ∈ Finset.range q,
          (κ.getD c 0 : ℝ) * (y i * ((((Ms.getD c []).getD i []).getD j 0 : ℤ) : ℝ) * y j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [getD_lin q κ Ms hκ hM i j]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ c ∈ Finset.range q, ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
          (κ.getD c 0 : ℝ) * (y i * ((((Ms.getD c []).getD i []).getD j 0 : ℤ) : ℝ) * y j) :=
        sum3_comm' _ _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- A corner witness: `b` passes the fast PSD check and `ent(b) = ∑_c κ_c M_c`. -/
def CornerOK (q r : ℕ) (Ms : List (List (List ℤ))) (κ : List ℤ) (b : Blk) : Prop :=
  κ.length ≤ q ∧ okF r b = true ∧ b.d.length ≤ r ∧ b.l.length ≤ r ∧ NBlk.entMat b = lin κ Ms

lemma corner_nonneg {q r : ℕ} {Ms : List (List (List ℤ))} (hM : Ms.length ≤ q) {κ : List ℤ} {b : Blk}
    (h : CornerOK q r Ms κ b) (y : ℕ → ℝ) :
    0 ≤ ∑ c ∈ Finset.range q, (κ.getD c 0 : ℝ) * qf r (Ms.getD c []) y := by
  obtain ⟨hκ, hok, hd, hl, he⟩ := h
  rw [← qf_lin r q κ Ms hκ hM y, ← he]
  unfold qf
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [NBlk.getD_entMat r b hd hl i j]]
  exact Blk.qf_ent_nonneg (okF_sound hok) y

/-- `w` is a nonnegative combination of the corners, in the dual sense: every linear functional that is
nonnegative at all corners `κ ∈ κs` is nonnegative at `w`. -/
def AffOK (q : ℕ) (w : ℕ → ℝ) (κs : List (List ℤ)) : Prop :=
  ∀ Q : ℕ → ℝ, (∀ κ ∈ κs, 0 ≤ ∑ c ∈ Finset.range q, (κ.getD c 0 : ℝ) * Q c) →
    0 ≤ ∑ c ∈ Finset.range q, w c * Q c

/-- A checked `K`-block: integer basis `N` (rows of length `≤ r`), the `q` component reduced blocks `Ms`
(`r × r`, not PSD individually), and one PSD witness per corner. -/
structure KOK (q r : ℕ) (κs : List (List ℤ)) (N : List (List ℤ)) (Ms : List (List (List ℤ)))
    (bs : List Blk) : Prop where
  hN : N.all (fun row => decide (row.length ≤ r)) = true
  hE : Ms.all (fun M => decide (M.length ≤ r) && M.all fun row => decide (row.length ≤ r)) = true
  hq : Ms.length ≤ q
  hc : List.Forall₂ (CornerOK q r Ms) κs bs

namespace KOK

variable {q r : ℕ} {κs : List (List ℤ)} {N : List (List ℤ)} {Ms : List (List (List ℤ))} {bs : List Blk}

lemma rowsN (h : KOK q r κs N Ms bs) : ∀ row ∈ N, row.length ≤ r := by
  have := h.hN
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this

lemma rowsE (h : KOK q r κs N Ms bs) (c : ℕ) :
    (Ms.getD c []).length ≤ r ∧ ∀ row ∈ Ms.getD c [], row.length ≤ r := by
  have hE := h.hE
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hE
  by_cases hc : c < Ms.length
  · rw [List.getD_eq_getElem _ _ hc]
    exact hE _ (List.getElem_mem hc)
  · push Not at hc
    rw [NBlk.getD_nil_of_le Ms [] c hc]
    simp

/-- **Positivity at `w`** of the component quadratic forms, from the corner witnesses. -/
lemma qf_nonneg {w : ℕ → ℝ} (hw : AffOK q w κs) (h : KOK q r κs N Ms bs) (y : ℕ → ℝ) :
    0 ≤ ∑ c ∈ Finset.range q, w c * qf r (Ms.getD c []) y := by
  refine hw (fun c => qf r (Ms.getD c []) y) fun κ hκ => ?_
  obtain ⟨b, hb⟩ := exists_of_forall₂ h.hc κ hκ
  exact corner_nonneg h.hq hb y

end KOK

/-! ## Congruence: `N · E · Nᵀ` -/

/-- `N · E · Nᵀ`, row by row. -/
def expandE (N E : List (List ℤ)) : List (List ℤ) :=
  N.map fun row => N.map fun rb => NBlk.dot (NBlk.vecMat row E) rb

lemma getD_expandE {r : ℕ} {N E : List (List ℤ)} (hN : ∀ row ∈ N, row.length ≤ r)
    (hE : E.length ≤ r) (hEr : ∀ row ∈ E, row.length ≤ r) {a c : ℕ} (ha : a < N.length)
    (hc : c < N.length) :
    ((expandE N E).getD a []).getD c 0
      = ∑ j ∈ Finset.range r, (∑ i ∈ Finset.range r, (N.getD a []).getD i 0 * (E.getD i []).getD j 0)
          * (N.getD c []).getD j 0 := by
  have hNa : N.getD a [] ∈ N := by rw [List.getD_eq_getElem N [] ha]; exact List.getElem_mem ha
  have hNc : N.getD c [] ∈ N := by rw [List.getD_eq_getElem N [] hc]; exact List.getElem_mem hc
  have hrow : (expandE N E).getD a [] = N.map fun rb => NBlk.dot (NBlk.vecMat (N.getD a []) E) rb := by
    rw [List.getD_eq_getElem N [] ha]
    exact NBlk.getD_map_lt _ N a ha
  rw [hrow, NBlk.getD_map_lt' _ N c hc, ← List.getD_eq_getElem N [] hc,
    NBlk.dot_eq_sum r _ _ (NBlk.length_vecMat_le r _ _ hEr) (hN _ hNc)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [NBlk.getD_vecMat r _ _ (hN _ hNa) hE j]

/-- **Congruence**: `xᵀ (N E Nᵀ) x = yᵀ E y` with `y = Nᵀ x`. -/
lemma qf_expandE {r m : ℕ} {N E : List (List ℤ)} (hN : ∀ row ∈ N, row.length ≤ r)
    (hE : E.length ≤ r) (hEr : ∀ row ∈ E, row.length ≤ r) (hm : m ≤ N.length) (x : ℕ → ℝ) :
    ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m, x a * ((((expandE N E).getD a []).getD c 0 : ℤ) : ℝ) * x c
      = qf r E (fun i => ∑ a ∈ Finset.range m, (((N.getD a []).getD i 0 : ℤ) : ℝ) * x a) := by
  have key : ∀ a ∈ Finset.range m, ∀ c ∈ Finset.range m,
      x a * ((((expandE N E).getD a []).getD c 0 : ℤ) : ℝ) * x c
        = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
          x a * (((N.getD a []).getD i 0 : ℤ) : ℝ) * (((E.getD i []).getD j 0 : ℤ) : ℝ)
            * (((N.getD c []).getD j 0 : ℤ) : ℝ) * x c := by
    intro a ha c hc
    have ha' := Finset.mem_range.1 ha
    have hc' := Finset.mem_range.1 hc
    rw [getD_expandE hN hE hEr (by omega) (by omega), Finset.sum_comm]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => key a ha c hc, NBlk.sum4_comm]
  unfold qf
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- Symmetry of a list matrix from the transpose check. -/
lemma sym_of_transpose {m : ℕ} {X : List (List ℤ)} (h : X.map (List.take m) = transposeSq m X)
    {i j : ℕ} (hi : i < m) (hj : j < m) : (X.getD i []).getD j 0 = (X.getD j []).getD i 0 := by
  have h1 : ((X.map (List.take m)).getD i []).getD j 0 = (X.getD i []).getD j 0 := by
    rw [getD_map_list (List.take m) (by simp)]
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h, transposeSq_getD m X i hi j] at h1
  exact h1.symm

lemma ent_noPiv (X : List (List ℤ)) (r a b : ℕ) :
    (⟨[], [], X⟩ : Blk).ent r a b = (X.getD a []).getD b 0 := by
  simp [Blk.ent, Blk.dq, Blk.lq, Blk.del]

end KB

namespace Cert3K

open KB

/-- The default SOS block. -/
def sDflt : SBlk := ⟨[], 0, [], Blk.empty⟩

/-- The kernel matrices of the `K`-certificate at the weights `w`: `∑_c w_c · F_{c,k}`. -/
noncomputable def FmK (q : ℕ) (cf : ℕ → Cert3) (w : ℕ → ℝ) (Lam : ℕ) (m : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin (m k)) (Fin (m k)) ℝ :=
  Matrix.of fun a b => ∑ c ∈ Finset.range q, w c * (((cf c).blk k).ent (m k) a b : ℝ) / Lam

/-- The minorant of the `K`-certificate at the weights `w`: `∑_c w_c · H_c`. -/
noncomputable def HK (q : ℕ) (cf : ℕ → Cert3) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ c ∈ Finset.range q, w c * (cf c).Hf x

/-- The energy bound of the `K`-certificate at the weights `w`: `∑_c w_c · e_c`. -/
noncomputable def eK (q : ℕ) (cf : ℕ → Cert3) (w : ℕ → ℝ) (Lam : ℕ) : ℝ :=
  ∑ c ∈ Finset.range q, w c * ((cf c).eps : ℝ) / Lam

lemma matDot_FmK (q : ℕ) (cf : ℕ → Cert3) (w : ℕ → ℝ) (Lam : ℕ) (m : ℕ → ℕ) (k : ℕ)
    (R : Matrix (Fin (m k)) (Fin (m k)) ℝ) :
    matDot (FmK q cf w Lam m k) R
      = ∑ c ∈ Finset.range q, w c * matDot (fmat (m k) Lam ((cf c).blk k)) R := by
  simp only [matDot, FmK, fmat, Matrix.of_apply]
  calc ∑ a : Fin (m k), ∑ b : Fin (m k),
          (∑ c ∈ Finset.range q, w c * (((cf c).blk k).ent (m k) a b : ℝ) / Lam) * R a b
      = ∑ a : Fin (m k), ∑ b : Fin (m k), ∑ c ∈ Finset.range q,
          w c * ((((cf c).blk k).ent (m k) a b : ℝ) / Lam * R a b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ a : Fin (m k), ∑ c ∈ Finset.range q, ∑ b : Fin (m k),
          w c * ((((cf c).blk k).ent (m k) a b : ℝ) / Lam * R a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ Finset.range q, ∑ a : Fin (m k), ∑ b : Fin (m k),
          w c * ((((cf c).blk k).ent (m k) a b : ℝ) / Lam * R a b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- The real-number algebra of the soundness proof, as an equation (cf. upstream `final_ineq`). -/
lemma final_eq {n' C Λ Hs eps A Ssum : ℝ} (hn : 3 ≤ n') (hC : 0 < C) (hΛ : 0 < Λ)
    (hev : 2 * (n' - 1) * C * Hs - 6 * (n' - 1) * eps - C * (6 * (n' - 1) * Λ * A)
      - 6 * (n' - 1) * C * Ssum = 0) :
    (Hs / Λ) / 3 - (eps / Λ) / C - A = Ssum / Λ := by
  have h2 : 2 * (n' - 1) ≠ 0 := by
    have : 0 < 2 * (n' - 1) := by linarith
    exact this.ne'
  have hz : Hs * C - 3 * eps - 3 * Λ * C * A - 3 * C * Ssum = 0 := by
    refine mul_left_cancel₀ h2 ?_
    linear_combination hev
  have e : (Hs / Λ) / 3 - (eps / Λ) / C - A - Ssum / Λ
      = (Hs * C - 3 * eps - 3 * Λ * C * A - 3 * C * Ssum) / (3 * Λ * C) := by
    have hΛ' : Λ ≠ 0 := hΛ.ne'
    have hC' : C ≠ 0 := hC.ne'
    field_simp
  rw [hz, zero_div] at e
  linarith

/-- The checked identity of one component certificate, evaluated (cf. upstream `hpt_gramCut`):
`(H(u)+H(v)+H(t))/3 - e/C(n,2) - ∑_k ⟨F_k, R_k⟩ = (SOS part)/Λ`. -/
lemma comp_eq (cf : Cert3) (n Lam K : ℕ) (m : ℕ → ℕ) (hn : cf.n = n) (hL : cf.Lam = Lam)
    (hK : cf.K = K) (hm : ∀ k < K, cf.m k = m k) (h3 : 3 ≤ n) (hLpos : 0 < Lam)
    (hz : chk cf.idE = true) (u v t : ℝ) :
    (cf.Hf u + cf.Hf v + cf.Hf t) / 3 - ((cf.eps : ℝ) / Lam) / (n.choose 2 : ℕ)
      - ∑ k ∈ Finset.range K, matDot (fmat (m k) Lam (cf.blk k)) (Rk n (m k) k u v t)
      = ((cf.S.map (sblkE cf.an cf.ad)).map fun e => e.ev u v t).sum / Lam := by
  have hev := chk_sound hz u v t
  simp only [Cert3.idE, ev_sub, ev_smul, ev_c, ev_hE, ev_ftotE, ev_sumE] at hev
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast h3
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    exact this.ne'
  have hLr : (0 : ℝ) < Lam := by exact_mod_cast hLpos
  have hC : (0 : ℝ) < (n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hFp : ∑ k ∈ Finset.range cf.K,
        ftotTerm cf.n (fun a b c => (fkE (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((n : ℝ) - 1) * Lam
        * ∑ k ∈ Finset.range K, matDot (fmat (m k) Lam (cf.blk k)) (Rk n (m k) k u v t) := by
    rw [hK, hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hm k (Finset.mem_range.1 hk)]
    exact (key_F (cf.blk k) k n hLr.ne' hn1 u v t).symm
  rw [hFp, hn] at hev
  push_cast at hev
  rw [Cert3.Hf_sum, hL]
  exact final_eq hnr hC hLr hev

lemma list_sum_map_getD {α : Type*} (f : α → ℝ) (d : α) :
    ∀ L : List α, (L.map f).sum = ∑ i ∈ Finset.range L.length, f (L.getD i d)
  | [] => by simp
  | x :: L => by
    rw [List.map_cons, List.sum_cons, list_sum_map_getD f d L, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma gramCut_of_gramOK {u v t : ℝ} (hg : GramOK u v t) : GramCut (-1) 1 u v t := by
  obtain ⟨hu, hv, ht, hd⟩ := hg
  have hu' := abs_le.1 ((sq_le_one_iff_abs_le_one u).1 hu)
  have hv' := abs_le.1 ((sq_le_one_iff_abs_le_one v).1 hv)
  have ht' := abs_le.1 ((sq_le_one_iff_abs_le_one t).1 ht)
  refine ⟨⟨hu, hv, ht, hd⟩, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

/-- The `w`-weighted SOS parts are nonnegative (cf. upstream `sos_sum_nonneg`, `sblkE_nonneg`). -/
lemma sos_comb_nonneg (q nS : ℕ) (cf : ℕ → Cert3) (w : ℕ → ℝ) (gs : ℕ → List ℕ) (σs : ℕ → ℕ)
    (zs : ℕ → List (ℕ × ℕ × ℕ))
    (hcf : ∀ c < q, (cf c).an = -1 ∧ (cf c).ad = 1 ∧ (cf c).S.length = nS)
    (hsh : ∀ c < q, ∀ i < nS, ((cf c).S.getD i sDflt).g = gs i ∧ ((cf c).S.getD i sDflt).σ = σs i ∧
      ((cf c).S.getD i sDflt).z = zs i)
    (hpos : ∀ i < nS, ∀ u v t : ℝ,
      0 ≤ ∑ c ∈ Finset.range q, w c * (sqfE ((cf c).S.getD i sDflt).B (zs i)).ev u v t)
    {u v t : ℝ} (hg : GramOK u v t) :
    0 ≤ ∑ c ∈ Finset.range q,
      w c * (((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum := by
  set U : ℕ → ℝ := fun i => varVal u v t (perm3 (σs i)).1
  set V : ℕ → ℝ := fun i => varVal u v t (perm3 (σs i)).2.1
  set T : ℕ → ℝ := fun i => varVal u v t (perm3 (σs i)).2.2
  have e1 : ∀ c ∈ Finset.range q,
      w c * (((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum
        = ∑ i ∈ Finset.range nS, (gE (-1) 1 (gs i)).ev (U i) (V i) (T i)
            * (w c * (sqfE ((cf c).S.getD i sDflt).B (zs i)).ev (U i) (V i) (T i)) := by
    intro c hc
    obtain ⟨han, had, hlen⟩ := hcf c (Finset.mem_range.1 hc)
    rw [List.map_map, list_sum_map_getD _ sDflt, hlen, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hg', hσ, hz⟩ := hsh c (Finset.mem_range.1 hc) i (Finset.mem_range.1 hi)
    simp only [Function.comp_apply, sblkE, ev_sbst, ev_mul, han, had, hg', hσ, hz]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_nonneg fun i hi => ?_
  rw [← Finset.mul_sum]
  refine mul_nonneg (gE_nonneg (-1) 1 (gs i) (gramCut_perm3 (-1) 1 (σs i) (gramCut_of_gramOK hg))) ?_
  exact hpos i (Finset.mem_range.1 hi) _ _ _

/-- **Soundness of a `K`-certificate (no cut).**  `q` rational component certificates `cf c` with shared
structure, checked identities `chk (cf c).idE`, and positivity of the `w`-weighted kernel and SOS blocks give
`e_K ≤ ∑_{i<j} H_K(⟪x i, x j⟫)` for all unit vectors `x 0, …, x (n-1)` of `ℝ³` (cf. upstream `sound`). -/
theorem soundK (q : ℕ) (cf : ℕ → Cert3) (w : ℕ → ℝ) (n Lam K nS : ℕ) (m : ℕ → ℕ)
    (gs : ℕ → List ℕ) (σs : ℕ → ℕ) (zs : ℕ → List (ℕ × ℕ × ℕ)) (hn : 3 ≤ n) (hL : 0 < Lam)
    (hcf : ∀ c < q, (cf c).n = n ∧ (cf c).Lam = Lam ∧ (cf c).an = -1 ∧ (cf c).ad = 1 ∧
      (cf c).K = K ∧ (cf c).S.length = nS ∧ chk (cf c).idE = true)
    (hm : ∀ c < q, ∀ k < K, (cf c).m k = m k)
    (hsh : ∀ c < q, ∀ i < nS, ((cf c).S.getD i sDflt).g = gs i ∧ ((cf c).S.getD i sDflt).σ = σs i ∧
      ((cf c).S.getD i sDflt).z = zs i)
    (hF : ∀ k < K, (FmK q cf w Lam m k).PosSemidef)
    (hS : ∀ i < nS, ∀ u v t : ℝ,
      0 ≤ ∑ c ∈ Finset.range q, w c * (sqfE ((cf c).S.getD i sDflt).B (zs i)).ev u v t)
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    eK q cf w Lam ≤ ∑ i, ∑ j ∈ Finset.Ioi i, HK q cf w ⟪x i, x j⟫ := by
  refine three_point_bound hn K m (FmK q cf w Lam m) hF (HK q cf w) (eK q cf w Lam) ?_ x hx
  intro u v t hg
  have hLr : (0 : ℝ) < Lam := by exact_mod_cast hL
  have hcomp : ∀ c ∈ Finset.range q,
      w c * ((cf c).Hf u + (cf c).Hf v + (cf c).Hf t) / 3
        - w c * ((cf c).eps : ℝ) / Lam / (n.choose 2 : ℕ)
        - w c * ∑ k ∈ Finset.range K, matDot (fmat (m k) Lam ((cf c).blk k)) (Rk n (m k) k u v t)
      = w c * (((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum / Lam := by
    intro c hc
    obtain ⟨h1, h2, -, -, h5, -, h7⟩ := hcf c (Finset.mem_range.1 hc)
    have := comp_eq (cf c) n Lam K m h1 h2 h5 (hm c (Finset.mem_range.1 hc)) hn hL h7 u v t
    rw [show w c * (((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum / Lam
        = w c * ((((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum / Lam) by ring,
      ← this]
    ring
  have hsos := sos_comb_nonneg q nS cf w gs σs zs
    (fun c hc => ⟨(hcf c hc).2.2.1, (hcf c hc).2.2.2.1, (hcf c hc).2.2.2.2.2.1⟩) hsh hS hg
  have hF' : ∑ k ∈ Finset.range K, matDot (FmK q cf w Lam m k) (Rk n (m k) k u v t)
      = ∑ c ∈ Finset.range q,
          w c * ∑ k ∈ Finset.range K, matDot (fmat (m k) Lam ((cf c).blk k)) (Rk n (m k) k u v t) := by
    simp only [matDot_FmK, Finset.mul_sum]
    exact Finset.sum_comm
  have htot : (HK q cf w u + HK q cf w v + HK q cf w t) / 3 - eK q cf w Lam / (n.choose 2 : ℕ)
      - ∑ k ∈ Finset.range K, matDot (FmK q cf w Lam m k) (Rk n (m k) k u v t)
      = (∑ c ∈ Finset.range q,
          w c * (((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum) / Lam := by
    rw [hF', Finset.sum_div, ← Finset.sum_congr rfl hcomp]
    simp only [HK, eK, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    refine congrArg₂ _ (congrArg₂ _ ?_ rfl) rfl
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have : 0 ≤ (∑ c ∈ Finset.range q,
      w c * (((cf c).S.map (sblkE (cf c).an (cf c).ad)).map fun e => e.ev u v t).sum) / Lam :=
    div_nonneg hsos hLr.le
  linarith

end Cert3K

namespace KB

open Cert3K

/-- **Kernel blocks**: the `w`-weighted kernel matrix of a checked `K`-block is positive semidefinite
(cf. upstream `fmat_psd`). -/
lemma FmK_psd {q r : ℕ} {cf : ℕ → Cert3} {w : ℕ → ℝ} {Lam : ℕ} {m : ℕ → ℕ} {k : ℕ}
    {κs : List (List ℤ)} {N : List (List ℤ)} {Ms : List (List (List ℤ))} {bs : List Blk}
    (hw : AffOK q w κs) (h : KOK q r κs N Ms bs) (X : ℕ → List (List ℤ))
    (hb : ∀ c < q, (cf c).blk k = ⟨[], [], X c⟩) (hX : ∀ c < q, X c = expandE N (Ms.getD c []))
    (hsym : ∀ c < q, (X c).map (List.take (m k)) = transposeSq (m k) (X c))
    (hm : m k ≤ N.length) : (FmK q cf w Lam m k).PosSemidef := by
  have hent : ∀ c ∈ Finset.range q, ∀ a b : ℕ, ((cf c).blk k).ent (m k) a b = ((X c).getD a []).getD b 0 := by
    intro c hc a b
    rw [hb c (Finset.mem_range.1 hc), ent_noPiv]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [FmK, Matrix.of_apply, star_trivial]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hent c hc, hent c hc, sym_of_transpose (hsym c (Finset.mem_range.1 hc)) j.2 i.2]
  · intro x
    set x' : ℕ → ℝ := fun a => if ha : a < m k then x ⟨a, ha⟩ else 0 with hx'
    have hx'' : ∀ i : Fin (m k), x' i = x i := fun i => by simp [hx', i.2]
    have h0 := h.qf_nonneg hw (fun i => ∑ a ∈ Finset.range (m k), (((N.getD a []).getD i 0 : ℤ) : ℝ) * x' a)
    have h1 : ∀ c ∈ Finset.range q, w c * qf r (Ms.getD c [])
          (fun i => ∑ a ∈ Finset.range (m k), (((N.getD a []).getD i 0 : ℤ) : ℝ) * x' a)
        = ∑ a ∈ Finset.range (m k), ∑ b ∈ Finset.range (m k),
            x' a * (w c * ((((X c).getD a []).getD b 0 : ℤ) : ℝ)) * x' b := by
      intro c hc
      have hc' := Finset.mem_range.1 hc
      rw [← qf_expandE h.rowsN (h.rowsE c).1 (h.rowsE c).2 hm x', ← hX c hc', Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [Finset.sum_congr rfl h1, ← KB.sum3_comm' (Finset.range (m k)) (Finset.range (m k)) (Finset.range q)
      (fun a b c => x' a * (w c * ((((X c).getD a []).getD b 0 : ℤ) : ℝ)) * x' b)] at h0
    have h2 := div_nonneg h0 (Nat.cast_nonneg (α := ℝ) Lam)
    have e : (∑ a ∈ Finset.range (m k), ∑ b ∈ Finset.range (m k), ∑ c ∈ Finset.range q,
          x' a * (w c * ((((X c).getD a []).getD b 0 : ℤ) : ℝ)) * x' b) / Lam
        = dotProduct (star x) (Matrix.mulVec (FmK q cf w Lam m k) x) := by
      rw [← sum_fin_eq_range (m k) (fun a b => ∑ c ∈ Finset.range q,
          x' a * (w c * ((((X c).getD a []).getD b 0 : ℤ) : ℝ)) * x' b), Finset.sum_div]
      simp only [dotProduct, Matrix.mulVec, FmK, Matrix.of_apply, star_trivial, Pi.star_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [hent c hc, hx'', hx'']
      ring
    rw [e] at h2
    exact h2

/-- **SOS blocks**: the `w`-weighted quadratic form of a checked `K`-block, in the monomials `zs`, is
nonnegative (`sqfE` on the expanded component blocks). -/
lemma sqf_nonneg {q r : ℕ} {w : ℕ → ℝ} {κs : List (List ℤ)} {N : List (List ℤ)}
    {Ms : List (List (List ℤ))} {bs : List Blk} (hw : AffOK q w κs) (h : KOK q r κs N Ms bs)
    (B : ℕ → Blk) (hB : ∀ c < q, B c = ⟨[], [], expandE N (Ms.getD c [])⟩)
    (zs : List (ℕ × ℕ × ℕ)) (hz : zs.length ≤ N.length) (u v t : ℝ) :
    0 ≤ ∑ c ∈ Finset.range q, w c * (sqfE (B c) zs).ev u v t := by
  have e : ∀ c ∈ Finset.range q, w c * (sqfE (B c) zs).ev u v t
      = w c * qf r (Ms.getD c [])
          (fun i => ∑ a ∈ Finset.range zs.length, (((N.getD a []).getD i 0 : ℤ) : ℝ) * zval zs u v t a) := by
    intro c hc
    have hc' := Finset.mem_range.1 hc
    rw [← qf_expandE h.rowsN (h.rowsE c).1 (h.rowsE c).2 hz, ev_sqfE, hB c hc']
    simp [Blk.dq, Blk.del]
  rw [Finset.sum_congr rfl e]
  exact h.qf_nonneg hw _

end KB

end Cert
end ThomsonN7
