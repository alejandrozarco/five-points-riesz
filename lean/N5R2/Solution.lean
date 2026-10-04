import N5R2.Main

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`riesz2Energy` ← `coulombEnergy`. -/

/-!
# Solution of `N5R2/Challenge.lean`

Same statements, same definitions: `ThomsonN7.R3/SphereConfig` come from the regenerated upstream preamble
`ThomsonGen.Preamble`, which `N5R2/Challenge.lean` imports as well, and `FivePointsRiesz2.riesz2Energy` and
`FivePointsRiesz2.triBipyramid` below are the challenge's definitions verbatim (definitionally `N5R2.riesz2Energy` and
`N5R2.triBipyramid`).
-/

open Real

namespace FivePointsRiesz2

open ThomsonN7

/-- Riesz `s = 2` energy `∑_{i<j} ‖x i - x j‖⁻²`. -/
noncomputable def riesz2Energy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (‖x i - x j‖ ^ 2)⁻¹

/-- The triangular bipyramid: the poles `±e₃` and an equilateral triangle on the equator. -/
noncomputable def triBipyramid : Fin 5 → R3 :=
  ![!₂[0, 0, 1], !₂[0, 0, -1], !₂[1, 0, 0], !₂[-1 / 2, √3 / 2, 0], !₂[-1 / 2, -(√3 / 2), 0]]

theorem five_riesz2 :
    ∀ x ∈ SphereConfig 5, riesz2Energy triBipyramid ≤ riesz2Energy x :=
  N5R2.five_riesz2

theorem five_riesz2_unique :
    ∀ x ∈ SphereConfig 5, riesz2Energy x = riesz2Energy triBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 5)), ∀ i, x i = g (triBipyramid (σ i)) :=
  N5R2.five_riesz2_unique

end FivePointsRiesz2
