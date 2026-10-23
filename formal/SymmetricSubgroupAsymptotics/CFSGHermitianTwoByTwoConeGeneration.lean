import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoScalars

/-! The literal Hermitian rank-one cone generates the full additive
coefficient group. This is an additive generation theorem in every
characteristic, not a dimension or cardinality surrogate for generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem axis0_eq_rankOne (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (a : K) (ha : sigma a = a) :
    axis0 sigma a ha = rankOneParameter sigma hsigma a ha ![1, 0] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axis0, rankOneParameter, rankOne, Matrix.of_apply]

theorem eq_top_of_rankOne_parameters (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (P : AddSubgroup (parameters sigma))
    (hP : ∀ (a : K) (ha : sigma a = a) (v : Fin 2 → K),
      rankOneParameter sigma hsigma a ha v ∈ P) : P = ⊤ := by
  apply eq_top_of_axes_rays sigma hsigma P
  · intro a ha
    rw [axis0_eq_rankOne sigma hsigma a ha]
    exact hP a ha ![1, 0]
  · intro a ha
    rw [axis1_eq_rankOne sigma hsigma a ha]
    exact hP a ha ![0, 1]
  · intro x
    have hx := hP 1 (map_one sigma) ![1, sigma x]
    simpa only [← fixedScaleHom_ray sigma hsigma, fixedScaleHom_one] using hx

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
