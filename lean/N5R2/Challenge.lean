import ThomsonGen.Preamble

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`riesz2Energy` ← `coulombEnergy`; the statements ← `thomson_seven`, `thomson_seven_unique`. -/

/-!
# Riesz `s = 2` energy of 5 points on the sphere (challenge statement)

Among all configurations of 5 pairwise distinct unit vectors in `ℝ³`, the triangular bipyramid minimises the Riesz
`s = 2` energy `∑_{i<j} ‖x i − x j‖⁻²`, uniquely up to an orthogonal map of `ℝ³` and a relabelling of the points.

The definitions `R3` and `SphereConfig` (namespace `ThomsonN7`) are those of the Coulomb formalisation of seven points,
imported from `ThomsonGen/Preamble.lean`, which `regen.sh` regenerates from upstream (huwngtran/thomson-n7-lean @
25f2fa5) and checks against `ThomsonGen/scripts/generated.sha256`. `riesz2Energy` is the Riesz `s = 2` energy, adapted
from upstream `coulombEnergy`; the statements follow upstream `thomson_seven` and `thomson_seven_unique`. Injectivity in
`SphereConfig` rules out coincident points (where Lean's `0⁻¹ = 0`).
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
    ∀ x ∈ SphereConfig 5, riesz2Energy triBipyramid ≤ riesz2Energy x := by
  sorry

theorem five_riesz2_unique :
    ∀ x ∈ SphereConfig 5, riesz2Energy x = riesz2Energy triBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 5)), ∀ i, x i = g (triBipyramid (σ i)) := by
  sorry

end FivePointsRiesz2
