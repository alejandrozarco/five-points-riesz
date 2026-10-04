import N5R1.Bound
import N5R1Minor.Minor
import ThomsonGen.GV

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
the final step of `five_coulomb_unique` (obtaining the isometry from the Gram match) ← `Glue.seven_unique`; the
description of the statement below ← the docstring of `thomson_seven_unique`. `coulombEnergy` is upstream's own
definition (regenerated preamble). -/

/-!
# N = 5, Coulomb (s = 1): the triangular bipyramid is the unique minimiser

Among all configurations of 5 pairwise distinct unit vectors in `ℝ³`, the triangular bipyramid minimises the
Coulomb energy `∑_{i<j} ‖x i − x j‖⁻¹` (upstream `ThomsonN7.coulombEnergy`; minimum `1/2 + 3√2 + √3`), uniquely up to
an orthogonal map of `ℝ³` and a relabelling of the points.

* Minimality (`five_coulomb`): for unit vectors with `t = ⟪x i, x j⟫ < 1`, `‖x i − x j‖⁻¹ = 1/√(2 − 2t) ≥ H(t)`
  (`H_le`), and `∑_{i<j} H(t_ij) ≥ 1/2 + 3√2 + √3` is the three-point bound `bound`.
* Uniqueness (`five_coulomb_unique`): at equality every `t_ij` is an equality point of `H ≤ φ₁`, so
  `t_ij ∈ {-1, -1/2, 0}` (`H_eq_iff`), where `φ₁ = 1/2, √3/3, √2/2`.  Some pair is antipodal: otherwise
  `φ₁(t) = √2/2 + t (√2 − 2√3/3)` at every pair, and with `∑ t_ij = N/2`, `N ∈ ℤ`, the energy forces
  `-5 < N < -4`.  After relabelling the antipodal pair is `(0, 1)`.  Then `t_0r = t_1r = 0` for `r ≥ 2`, the energy
  forces the `φ₁`-sum of the three equatorial pairs to be `√3`, which (rational bounds on `√2, √3`) leaves
  `t_23 = t_24 = t_34 = -1/2`.  The Gram matrices of `(x 0, x 2, x 3)` and of the bipyramid's `(0, 2, 3)` agree, which
  gives the isometry (`isometry_of_gram_fin3`); `x 1 = -x 0` and `x 4 = -x 2 - x 3` follow by linearity.

The combinatorial part follows `N5R2/Main.lean` (the `s = 2` case).
-/

open Real

namespace N5R1

open ThomsonN7 ThomsonN7.Base ThomsonN7.GV
open scoped RealInnerProductSpace

/-- The triangular bipyramid: poles `0, 1`, equatorial triangle `2, 3, 4`. -/
noncomputable def triBipyramid : Fin 5 → R3 :=
  ![!₂[0, 0, 1], !₂[0, 0, -1], !₂[1, 0, 0], !₂[-1/2, √3/2, 0], !₂[-1/2, -(√3/2), 0]]

/-! ## Sums over pairs of `Fin 5` -/

theorem sum_pairs (f : Fin 5 → Fin 5 → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, f i j =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 1 2 + f 1 3 + f 1 4 + f 2 3 + f 2 4 + f 3 4 := by
  have h0 : Finset.Ioi (0 : Fin 5) = {1, 2, 3, 4} := by decide
  have h1 : Finset.Ioi (1 : Fin 5) = {2, 3, 4} := by decide
  have h2 : Finset.Ioi (2 : Fin 5) = {3, 4} := by decide
  have h3 : Finset.Ioi (3 : Fin 5) = {4} := by decide
  have h4 : Finset.Ioi (4 : Fin 5) = ∅ := by decide
  simp only [Fin.sum_univ_five, h0, h1, h2, h3, h4]
  simp
  ring

theorem sum_sq_symm (F : Fin 5 → Fin 5 → ℝ) (hF : ∀ i j, F i j = F j i) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, F i j := by
  rw [sum_pairs]
  simp only [Fin.sum_univ_five]
  linarith [hF 1 0, hF 2 0, hF 3 0, hF 4 0, hF 2 1, hF 3 1, hF 4 1, hF 3 2, hF 4 2, hF 4 3]

/-- The energy is invariant under relabelling. -/
theorem coulombEnergy_comp (x : Fin 5 → R3) (τ : Equiv.Perm (Fin 5)) :
    coulombEnergy (x ∘ τ) = coulombEnergy x := by
  set F : Fin 5 → Fin 5 → ℝ := fun a b => ‖x a - x b‖⁻¹ with hFdef
  have hF : ∀ a b, F a b = F b a := fun a b => by simp only [hFdef, norm_sub_rev]
  have hd : ∀ a, F a a = 0 := fun a => by simp [hFdef]
  have e1 := sum_sq_symm F hF
  have e2 := sum_sq_symm (fun a b => F (τ a) (τ b)) (fun a b => hF _ _)
  have e3 : ∑ a, ∑ b, F (τ a) (τ b) = ∑ a, ∑ b, F a b :=
    calc ∑ a, ∑ b, F (τ a) (τ b) = ∑ a, ∑ b, F (τ a) b :=
          Finset.sum_congr rfl fun a _ => Equiv.sum_comp τ (F (τ a))
      _ = ∑ a, ∑ b, F a b := Equiv.sum_comp τ (fun a => ∑ b, F a b)
  simp only [hd, Finset.sum_const_zero, zero_add] at e1 e2
  show ∑ a, ∑ b ∈ Finset.Ioi a, F (τ a) (τ b) = ∑ a, ∑ b ∈ Finset.Ioi a, F a b
  linarith

/-! ## The pair potential at the three equality points -/

/-- For unit vectors, `‖a - b‖⁻¹ = 1 / √(2 - 2⟪a, b⟫)`. -/
theorem inv_norm_sub {a b : R3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖a - b‖⁻¹ = 1 / √(2 - 2 * ⟪a, b⟫) := by
  rw [← norm_sub_sq_of_unit ha hb, Real.sqrt_sq (norm_nonneg _), one_div]

theorem phi_m1 : 1 / √(2 - 2 * (-1 : ℝ)) = 1 / 2 := by
  rw [show (2 : ℝ) - 2 * -1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem phi_mh : 1 / √(2 - 2 * (-1 / 2 : ℝ)) = √3 / 3 := by
  rw [show (2 : ℝ) - 2 * (-1 / 2) = 3 by norm_num]
  have h : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  rw [div_eq_div_iff hp.ne' (by norm_num : (3 : ℝ) ≠ 0), one_mul, h]

theorem phi_0 : 1 / √(2 - 2 * (0 : ℝ)) = √2 / 2 := by
  rw [show (2 : ℝ) - 2 * 0 = 2 by norm_num]
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_eq_div_iff hp.ne' (by norm_num : (2 : ℝ) ≠ 0), one_mul, h]

/-! ## The triangular bipyramid -/

/-- Gram matrix of the triangular bipyramid. -/
noncomputable def tbpGram : Fin 5 → Fin 5 → ℝ :=
  ![![1, -1, 0, 0, 0], ![-1, 1, 0, 0, 0], ![0, 0, 1, -1/2, -1/2], ![0, 0, -1/2, 1, -1/2],
    ![0, 0, -1/2, -1/2, 1]]

theorem inner_tbp (i j : Fin 5) : ⟪triBipyramid i, triBipyramid j⟫ = tbpGram i j := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> rw [inner_coord] <;> simp [triBipyramid, tbpGram] <;> linarith

theorem norm_tbp (i : Fin 5) : ‖triBipyramid i‖ = 1 := by
  have h := inner_tbp i i
  rw [real_inner_self_eq_norm_sq] at h
  have h1 : tbpGram i i = 1 := by fin_cases i <;> simp [tbpGram]
  rw [h1] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

theorem triBipyramid_mem : triBipyramid ∈ SphereConfig 5 := by
  refine ⟨norm_tbp, fun i j h => ?_⟩
  have h1 : ⟪triBipyramid i, triBipyramid j⟫ = 1 := by
    rw [h, real_inner_self_eq_norm_sq, norm_tbp]; norm_num
  rw [inner_tbp] at h1
  fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [tbpGram] at h1)

theorem coulombEnergy_triBipyramid : coulombEnergy triBipyramid = 1 / 2 + 3 * √2 + √3 := by
  unfold coulombEnergy
  rw [sum_pairs]
  simp only [inv_norm_sub (norm_tbp _) (norm_tbp _), inner_tbp]
  have g01 : tbpGram 0 1 = -1 := by simp [tbpGram]
  have g02 : tbpGram 0 2 = 0 := by simp [tbpGram]
  have g03 : tbpGram 0 3 = 0 := by simp [tbpGram]
  have g04 : tbpGram 0 4 = 0 := by simp [tbpGram]
  have g12 : tbpGram 1 2 = 0 := by simp [tbpGram]
  have g13 : tbpGram 1 3 = 0 := by simp [tbpGram]
  have g14 : tbpGram 1 4 = 0 := by simp [tbpGram]
  have g23 : tbpGram 2 3 = -1 / 2 := by simp [tbpGram]
  have g24 : tbpGram 2 4 = -1 / 2 := by simp [tbpGram]
  have g34 : tbpGram 3 4 = -1 / 2 := by simp [tbpGram]
  rw [g01, g02, g03, g04, g12, g13, g14, g23, g24, g34, phi_m1, phi_0, phi_mh]
  ring

/-! ## Unit-vector lemmas -/

theorem eq_neg_of_inner {a b : R3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (h : ⟪a, b⟫ = -1) : b = -a := by
  have h0 : ‖a + b‖ ^ 2 = 0 := by rw [norm_add_sq_real, ha, hb, h]; norm_num
  have h1 : a + b = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  calc b = (a + b) - a := by abel
    _ = -a := by rw [h1]; abel

theorem norm_add3_sq (a b c : R3) :
    ‖a + b + c‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + 2 * (⟪a, b⟫ + ⟪a, c⟫ + ⟪b, c⟫) := by
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left]; ring

theorem eq_of_inner_half {a b c : R3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : ⟪a, b⟫ = -1/2) (hac : ⟪a, c⟫ = -1/2) (hbc : ⟪b, c⟫ = -1/2) : c = -a - b := by
  have h0 : ‖a + b + c‖ ^ 2 = 0 := by rw [norm_add3_sq, ha, hb, hc, hab, hac, hbc]; norm_num
  have h1 : a + b + c = 0 := by
    rw [← norm_eq_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  calc c = (a + b + c) - a - b := by abel
    _ = -a - b := by rw [h1]; abel

/-! ## Minimality -/

/-- The minorant of `N5R1.Bound` and that of `N5R1Minor.Minor` are the same polynomial. -/
theorem Hn_eq_Hm (t : ℝ) : Hn t = Hm t := by
  unfold Hn Hn0 Hn1 Hn2 Hm Hm0 Hm1 Hm2; ring

section
variable {x : Fin 5 → R3}

theorem Hn_le_term (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x) {i j : Fin 5} (h : i ≠ j) :
    Hn ⟪x i, x j⟫ ≤ ‖x i - x j‖⁻¹ := by
  rw [inv_norm_sub (hx i) (hx j), Hn_eq_Hm]
  exact H_le (neg_one_le_inner_of_unit (hx i) (hx j)) (inner_lt_one_of_ne (hx i) (hx j) (hinj.ne h))

theorem le_coulombEnergy (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x) :
    (1 / 2 + 3 * √2 + √3 : ℝ) ≤ coulombEnergy x :=
  (bound x hx).trans (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ hj =>
    Hn_le_term hx hinj (ne_of_lt (Finset.mem_Ioi.1 hj)))

/-! ## Uniqueness -/

/-- At equality every inner product is an equality point of `H ≤ φ₁`. -/
theorem inner_mem_of_energy (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x)
    (hE : coulombEnergy x = 1 / 2 + 3 * √2 + √3) {i j : Fin 5} (hij : i ≠ j) :
    ⟪x i, x j⟫ = -1 ∨ ⟪x i, x j⟫ = -1 / 2 ∨ ⟪x i, x j⟫ = 0 := by
  suffices key : ∀ i j : Fin 5, i < j →
      ⟪x i, x j⟫ = -1 ∨ ⟪x i, x j⟫ = -1 / 2 ∨ ⟪x i, x j⟫ = 0 by
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · rw [real_inner_comm]; exact key j i h
  intro i j hij
  set d : Fin 5 → Fin 5 → ℝ := fun a b => ‖x a - x b‖⁻¹ - Hn ⟪x a, x b⟫ with hd
  have hd0 : ∀ a, ∀ b ∈ Finset.Ioi a, 0 ≤ d a b := fun a b hb =>
    sub_nonneg.2 (Hn_le_term hx hinj (ne_of_lt (Finset.mem_Ioi.1 hb)))
  have hsum : ∑ a, ∑ b ∈ Finset.Ioi a, d a b =
      coulombEnergy x - ∑ a, ∑ b ∈ Finset.Ioi a, Hn ⟪x a, x b⟫ := by
    simp only [hd, Finset.sum_sub_distrib]; rfl
  have hle : d i j ≤ ∑ a, ∑ b ∈ Finset.Ioi a, d a b :=
    (Finset.single_le_sum (hd0 i) (Finset.mem_Ioi.2 hij)).trans
      (Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.Ioi a, d a b)
        (fun a _ => Finset.sum_nonneg (hd0 a)) (Finset.mem_univ i))
  have hb := bound x hx
  have hdij : d i j = 0 := le_antisymm (by linarith) (hd0 i j (Finset.mem_Ioi.2 hij))
  have heq : Hm ⟪x i, x j⟫ = 1 / √(2 - 2 * ⟪x i, x j⟫) := by
    rw [← Hn_eq_Hm, ← inv_norm_sub (hx i) (hx j)]
    simp only [hd] at hdij; linarith
  exact (H_eq_iff (neg_one_le_inner_of_unit (hx i) (hx j))
    (inner_lt_one_of_ne (hx i) (hx j) (hinj.ne hij.ne))).1 heq

/-- At equality some pair is antipodal: otherwise `φ₁(t_ij) = √2/2 + t_ij (√2 - 2√3/3)` at every pair, and
`∑_{i<j} t_ij = N/2` with `N ∈ ℤ` would satisfy `-5 < N < -4`. -/
theorem exists_antipodal (hx : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x)
    (hE : coulombEnergy x = 1 / 2 + 3 * √2 + √3) : ∃ p q : Fin 5, p ≠ q ∧ ⟪x p, x q⟫ = -1 := by
  by_contra hno
  push Not at hno
  have hT : ∀ i j : Fin 5, i ≠ j → ∃ n : ℤ, ⟪x i, x j⟫ = n / 2 ∧
      1 / √(2 - 2 * ⟪x i, x j⟫) = √2 / 2 + ⟪x i, x j⟫ * (√2 - 2 * √3 / 3) := by
    intro i j hij
    rcases inner_mem_of_energy hx hinj hE hij with h | h | h
    · exact absurd h (hno i j hij)
    · exact ⟨-1, by rw [h]; norm_num, by rw [h, phi_mh]; ring⟩
    · exact ⟨0, by rw [h]; norm_num, by rw [h, phi_0]; ring⟩
  unfold coulombEnergy at hE
  rw [sum_pairs] at hE
  simp only [inv_norm_sub (hx _) (hx _)] at hE
  obtain ⟨n01, h01, k01⟩ := hT 0 1 (by decide)
  obtain ⟨n02, h02, k02⟩ := hT 0 2 (by decide)
  obtain ⟨n03, h03, k03⟩ := hT 0 3 (by decide)
  obtain ⟨n04, h04, k04⟩ := hT 0 4 (by decide)
  obtain ⟨n12, h12, k12⟩ := hT 1 2 (by decide)
  obtain ⟨n13, h13, k13⟩ := hT 1 3 (by decide)
  obtain ⟨n14, h14, k14⟩ := hT 1 4 (by decide)
  obtain ⟨n23, h23, k23⟩ := hT 2 3 (by decide)
  obtain ⟨n24, h24, k24⟩ := hT 2 4 (by decide)
  obtain ⟨n34, h34, k34⟩ := hT 3 4 (by decide)
  set c : ℝ := √2 - 2 * √3 / 3 with hc
  have hc0 : 0 < c := by linarith [lo2, hi3, hc]
  have key : ((n01 + n02 + n03 + n04 + n12 + n13 + n14 + n23 + n24 + n34 : ℤ) : ℝ) * c =
      1 - 4 * √2 + 2 * √3 := by
    push_cast
    linear_combination 2 * hE - 2 * (k01 + k02 + k03 + k04 + k12 + k13 + k14 + k23 + k24 + k34) -
      2 * c * (h01 + h02 + h03 + h04 + h12 + h13 + h14 + h23 + h24 + h34)
  set N : ℤ := n01 + n02 + n03 + n04 + n12 + n13 + n14 + n23 + n24 + n34 with hN
  have a1 : (N : ℝ) < -4 := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h hc0.le
    linarith [lo3, hc]
  have a2 : (-5 : ℝ) < N := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h hc0.le
    linarith [lo2, hi3, hc]
  have b1 : N < -4 := by exact_mod_cast a1
  have b2 : -5 < N := by exact_mod_cast a2
  omega

end

/-- The three inner products on the equator. -/
theorem equator_vals {a b c : ℝ} (ha : a = -1 ∨ a = -1 / 2 ∨ a = 0) (hb : b = -1 ∨ b = -1 / 2 ∨ b = 0)
    (hc : c = -1 ∨ c = -1 / 2 ∨ c = 0) (hE : 1 / √(2 - 2 * a) + 1 / √(2 - 2 * b) + 1 / √(2 - 2 * c) = √3) :
    a = -1 / 2 ∧ b = -1 / 2 ∧ c = -1 / 2 := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
    simp only [phi_m1, phi_mh, phi_0] at hE <;>
    first | (norm_num; done) | (exfalso; linarith [lo2, hi2, lo3, hi3])

/-- Uniqueness when the antipodal pair is `(0, 1)`. -/
theorem unique_normalized {y : Fin 5 → R3} (hy : ∀ i, ‖y i‖ = 1) (hinj : Function.Injective y)
    (hE : coulombEnergy y = 1 / 2 + 3 * √2 + √3) (h01 : ⟪y 0, y 1⟫ = -1) :
    ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ k, y k = g (triBipyramid k) := by
  have T : ∀ i j : Fin 5, i ≠ j → ⟪y i, y j⟫ = -1 ∨ ⟪y i, y j⟫ = -1 / 2 ∨ ⟪y i, y j⟫ = 0 :=
    fun i j h => inner_mem_of_energy hy hinj hE h
  have hy1 : y 1 = -y 0 := eq_neg_of_inner (hy 0) (hy 1) h01
  have hzero : ∀ r : Fin 5, r ≠ 0 → r ≠ 1 → ⟪y 0, y r⟫ = 0 ∧ ⟪y 1, y r⟫ = 0 := by
    intro r h0 h1
    have e : ⟪y 1, y r⟫ = -⟪y 0, y r⟫ := by rw [hy1, inner_neg_left]
    have A := T 0 r (Ne.symm h0)
    have B := T 1 r (Ne.symm h1)
    rw [e] at B ⊢
    rcases A with A | A | A <;> rcases B with B | B | B <;> constructor <;> linarith
  obtain ⟨z02, z12⟩ := hzero 2 (by decide) (by decide)
  obtain ⟨z03, z13⟩ := hzero 3 (by decide) (by decide)
  obtain ⟨z04, z14⟩ := hzero 4 (by decide) (by decide)
  have hE' : 1 / √(2 - 2 * ⟪y 2, y 3⟫) + 1 / √(2 - 2 * ⟪y 2, y 4⟫) + 1 / √(2 - 2 * ⟪y 3, y 4⟫) = √3 := by
    unfold coulombEnergy at hE
    rw [sum_pairs] at hE
    simp only [inv_norm_sub (hy _) (hy _)] at hE
    rw [h01, z02, z03, z04, z12, z13, z14, phi_m1, phi_0] at hE
    linarith
  obtain ⟨t23, t24, t34⟩ := equator_vals (T 2 3 (by decide)) (T 2 4 (by decide)) (T 3 4 (by decide)) hE'
  have hy4 : y 4 = -y 2 - y 3 := eq_of_inner_half (hy 2) (hy 3) (hy 4) t23 t24 t34
  -- the frames `(tbp 0, tbp 2, tbp 3)` and `(y 0, y 2, y 3)`
  set u : Fin 3 → R3 := ![triBipyramid 0, triBipyramid 2, triBipyramid 3] with hu
  set v : Fin 3 → R3 := ![y 0, y 2, y 3] with hv
  have hindep : LinearIndependent ℝ u := by
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [Matrix.det_fin_three]
    simp [Matrix.gram_apply, hu, inner_tbp, tbpGram, norm_tbp]
    norm_num
  have hgram : ∀ i j, ⟪u i, u j⟫ = ⟪v i, v j⟫ := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, hv, inner_tbp, tbpGram, norm_tbp, hy, z02, z03, t23, real_inner_comm (y 0), real_inner_comm (y 2)]
  obtain ⟨-, g, hg⟩ := isometry_of_gram_fin3 u v hindep hgram
  have g0 : g (triBipyramid 0) = y 0 := hg 0
  have g2 : g (triBipyramid 2) = y 2 := hg 1
  have g3 : g (triBipyramid 3) = y 3 := hg 2
  have p1 : triBipyramid 1 = -triBipyramid 0 :=
    eq_neg_of_inner (norm_tbp 0) (norm_tbp 1) (by rw [inner_tbp]; simp [tbpGram])
  have p4 : triBipyramid 4 = -triBipyramid 2 - triBipyramid 3 :=
    eq_of_inner_half (norm_tbp 2) (norm_tbp 3) (norm_tbp 4) (by rw [inner_tbp]; simp [tbpGram])
      (by rw [inner_tbp]; simp [tbpGram]) (by rw [inner_tbp]; simp [tbpGram])
  refine ⟨g, fun k => ?_⟩
  fin_cases k
  · exact g0.symm
  · show y 1 = g (triBipyramid 1)
    rw [hy1, p1, map_neg, g0]
  · exact g2.symm
  · exact g3.symm
  · show y 4 = g (triBipyramid 4)
    rw [hy4, p4, map_sub, map_neg, g2, g3]

/-! ## Main theorems -/

/-- **Coulomb, N = 5 (minimality).** Among all configurations of 5 distinct points on the unit sphere, the
triangular bipyramid minimises `∑_{i<j} ‖x i - x j‖⁻¹`; the minimum is `1/2 + 3√2 + √3`. -/
theorem five_coulomb : ∀ x ∈ SphereConfig 5, coulombEnergy triBipyramid ≤ coulombEnergy x := by
  intro x ⟨hx, hinj⟩
  rw [coulombEnergy_triBipyramid]
  exact le_coulombEnergy hx hinj

/-- **Coulomb, N = 5 (uniqueness).** Every minimiser is the triangular bipyramid up to an orthogonal map of `ℝ³`
and a relabelling. -/
theorem five_coulomb_unique : ∀ x ∈ SphereConfig 5, coulombEnergy x = coulombEnergy triBipyramid →
    ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 5)), ∀ i, x i = g (triBipyramid (σ i)) := by
  intro x ⟨hx, hinj⟩ hE
  rw [coulombEnergy_triBipyramid] at hE
  obtain ⟨p, q, hpq, hpq'⟩ := exists_antipodal hx hinj hE
  -- a relabelling `τ` with `τ 0 = p`, `τ 1 = q`
  set q' := Equiv.swap 0 p q with hq'
  have hq'0 : q' ≠ 0 := by
    intro h
    have : Equiv.swap 0 p q' = Equiv.swap 0 p 0 := by rw [h]
    rw [hq', Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact hpq this.symm
  set τ : Equiv.Perm (Fin 5) := Equiv.swap 0 p * Equiv.swap 1 q' with hτ
  have τ0 : τ 0 = p := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) hq'0.symm,
      Equiv.swap_apply_left]
  have τ1 : τ 1 = q := by
    rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, hq', Equiv.swap_apply_self]
  have hy : ∀ i, ‖(x ∘ τ) i‖ = 1 := fun i => hx _
  have hyinj : Function.Injective (x ∘ τ) := hinj.comp τ.injective
  have hyE : coulombEnergy (x ∘ τ) = 1 / 2 + 3 * √2 + √3 := by rw [coulombEnergy_comp]; exact hE
  have hy01 : ⟪(x ∘ τ) 0, (x ∘ τ) 1⟫ = -1 := by simp only [Function.comp, τ0, τ1]; exact hpq'
  obtain ⟨g, hg⟩ := unique_normalized hy hyinj hyE hy01
  refine ⟨g, τ.symm, fun i => ?_⟩
  rw [← hg]
  simp

end N5R1
