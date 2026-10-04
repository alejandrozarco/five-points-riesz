import ThomsonGen.Preamble

/-!
# Coulomb energy of 5 points on the sphere (challenge statement)

Among all configurations of 5 pairwise distinct unit vectors in `ℝ³`, the triangular bipyramid minimises the Coulomb
energy `∑_{i<j} ‖x i − x j‖⁻¹`, uniquely up to an orthogonal map of `ℝ³` and a relabelling of the points.

The definitions `R3`, `SphereConfig` and `coulombEnergy` (namespace `ThomsonN7`) are those of the Coulomb formalisation
of seven points, imported from `ThomsonGen/Preamble.lean`, which `regen.sh` regenerates from upstream
(huwngtran/thomson-n7-lean @ 25f2fa5) and checks against `ThomsonGen/scripts/generated.sha256`; `coulombEnergy` is
upstream's own definition. The statements follow upstream `thomson_seven` and `thomson_seven_unique`. Injectivity in
`SphereConfig` rules out coincident points (where Lean's `0⁻¹ = 0`).
-/

open Real

namespace FivePointsCoulomb

open ThomsonN7

/-- The triangular bipyramid: the poles `±e₃` and an equilateral triangle on the equator. -/
noncomputable def triBipyramid : Fin 5 → R3 :=
  ![!₂[0, 0, 1], !₂[0, 0, -1], !₂[1, 0, 0], !₂[-1 / 2, √3 / 2, 0], !₂[-1 / 2, -(√3 / 2), 0]]

theorem five_coulomb :
    ∀ x ∈ SphereConfig 5, coulombEnergy triBipyramid ≤ coulombEnergy x := by
  sorry

theorem five_coulomb_unique :
    ∀ x ∈ SphereConfig 5, coulombEnergy x = coulombEnergy triBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 5)), ∀ i, x i = g (triBipyramid (σ i)) := by
  sorry

end FivePointsCoulomb
