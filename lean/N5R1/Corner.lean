import Mathlib

/-!
# Positivity of affine functions on a box, from the corners

The Coulomb (`s = 1`) certificate for five points has numbers in `ℚ(√2, √3)`. Every quantity the argument needs is
affine in `p = (√2, √3, √6)` once each field element is written `a + b√2 + c√3 + d√6` with rational `a, b, c, d`.
An affine function on a box `[lo₁, hi₁] × [lo₂, hi₂] × [lo₃, hi₃]` attains its minimum at a corner, so positivity at
the 8 corners (rational checks) gives positivity at `p`. For a family of quadratic forms affine in `p`, the same holds
pointwise in the vector, hence positive semidefiniteness at the corners gives it at `p`.

* `affine_pos_of_corners`, `affine_nonneg_of_corners`: the scalar statements;
* `corner`: the corner of the box selected by three Booleans.
-/

namespace N5R1

/-- The corner of the box `[lo, hi]` (three coordinates) selected by `b`: `hi i` where `b i`, else `lo i`. -/
def corner (lo hi : Fin 3 → ℝ) (b : Fin 3 → Bool) : Fin 3 → ℝ := fun i => if b i then hi i else lo i

/-- The affine function `a + ∑ cᵢ pᵢ`. -/
def aff (a : ℝ) (c p : Fin 3 → ℝ) : ℝ := a + ∑ i, c i * p i

/-- For `lo ≤ p ≤ hi`, the affine function is at least its value at the corner that takes, in each coordinate, the
endpoint where `cᵢ xᵢ` is smallest. -/
theorem aff_ge_corner (a : ℝ) (c lo hi p : Fin 3 → ℝ) (hlo : ∀ i, lo i ≤ p i) (hhi : ∀ i, p i ≤ hi i) :
    aff a c (corner lo hi fun i => decide (c i < 0)) ≤ aff a c p := by
  unfold aff
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro i _
  unfold corner
  by_cases h : c i < 0
  · simp only [h, decide_true, ite_true]
    exact mul_le_mul_of_nonpos_left (hhi i) h.le
  · simp only [h, decide_false, ite_false, Bool.false_eq_true]
    exact mul_le_mul_of_nonneg_left (hlo i) (not_lt.mp h)

/-- **Positivity from the corners.** -/
theorem affine_pos_of_corners (a : ℝ) (c lo hi p : Fin 3 → ℝ) (hlo : ∀ i, lo i ≤ p i) (hhi : ∀ i, p i ≤ hi i)
    (hc : ∀ b : Fin 3 → Bool, 0 < aff a c (corner lo hi b)) : 0 < aff a c p :=
  lt_of_lt_of_le (hc _) (aff_ge_corner a c lo hi p hlo hhi)

/-- **Nonnegativity from the corners.** -/
theorem affine_nonneg_of_corners (a : ℝ) (c lo hi p : Fin 3 → ℝ) (hlo : ∀ i, lo i ≤ p i)
    (hhi : ∀ i, p i ≤ hi i) (hc : ∀ b : Fin 3 → Bool, 0 ≤ aff a c (corner lo hi b)) : 0 ≤ aff a c p :=
  le_trans (hc _) (aff_ge_corner a c lo hi p hlo hhi)

end N5R1
