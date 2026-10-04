import N5R1.Main

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean`: the statements follow
upstream `thomson_seven` / `thomson_seven_unique`, and `coulombEnergy` is upstream's own definition. -/

/-!
# Solution of `N5R1/Challenge.lean`

Same statements, same definitions: `ThomsonN7.R3/SphereConfig/coulombEnergy` come from the regenerated upstream
preamble `ThomsonGen.Preamble`, which `N5R1/Challenge.lean` imports as well, and `FivePointsCoulomb.triBipyramid` below
is the challenge's definition verbatim (definitionally `N5R1.triBipyramid`).
-/

open Real

namespace FivePointsCoulomb

open ThomsonN7

/-- The triangular bipyramid: the poles `±e₃` and an equilateral triangle on the equator. -/
noncomputable def triBipyramid : Fin 5 → R3 :=
  ![!₂[0, 0, 1], !₂[0, 0, -1], !₂[1, 0, 0], !₂[-1 / 2, √3 / 2, 0], !₂[-1 / 2, -(√3 / 2), 0]]

theorem five_coulomb :
    ∀ x ∈ SphereConfig 5, coulombEnergy triBipyramid ≤ coulombEnergy x :=
  N5R1.five_coulomb

theorem five_coulomb_unique :
    ∀ x ∈ SphereConfig 5, coulombEnergy x = coulombEnergy triBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 5)), ∀ i, x i = g (triBipyramid (σ i)) :=
  N5R1.five_coulomb_unique

end FivePointsCoulomb
