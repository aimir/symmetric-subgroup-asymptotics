import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRootLines
import SymmetricSubgroupAsymptotics.CFSGTwoCoordinateRays
import Mathlib.Tactic.LinearCombination

/-! A nonzero Hermitian rank-one coefficient determines its exact
quadratic-field projective ray. The proof uses one nonzero coordinate
of the displayed vector and two entries of the SAME matrix; it does
not identify rays from determinants or a counting argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem rankOneParameter_ne_zero (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (a : K) (ha : sigma a = a)
    (ha0 : a ≠ 0) (v : Fin 2 → K) (hv : v ≠ 0) :
    rankOneParameter sigma hsigma a ha v ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hvk : v k ≠ 0 := hk
  have hsk : sigma (v k) ≠ 0 := by
    intro h
    apply hvk
    apply sigma.injective
    simpa only [map_zero] using h
  intro h
  have he := congrArg (fun A : parameters sigma => A.val k k) h
  change a * v k * sigma (v k) = 0 at he
  exact mul_ne_zero (mul_ne_zero ha0 hvk) hsk he

theorem span_eq_of_rankOneParameter_eq (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x)
    (a b : K) (ha : sigma a = a) (hb : sigma b = b) (ha0 : a ≠ 0)
    (v w : Fin 2 → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (he : rankOneParameter sigma hsigma a ha v = rankOneParameter sigma hsigma b hb w) :
    (K ∙ v : Submodule K (Fin 2 → K)) = K ∙ w := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hvk : v k ≠ 0 := hk
  have hsk : sigma (v k) ≠ 0 := by
    intro h
    apply hvk
    apply sigma.injective
    simpa only [map_zero] using h
  have h0 := congrArg (fun A : parameters sigma => A.val 0 k) he
  have h1 := congrArg (fun A : parameters sigma => A.val 1 k) he
  change a * v 0 * sigma (v k) = b * w 0 * sigma (w k) at h0
  change a * v 1 * sigma (v k) = b * w 1 * sigma (w k) at h1
  have hprod : (a * sigma (v k)) * (v 0 * w 1 - v 1 * w 0) = 0 := by
    linear_combination w 1 * h0 - w 0 * h1
  have hdet : v 0 * w 1 - v 1 * w 0 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero ha0 hsk)
  obtain ⟨c, hc⟩ := CFSGTwoCoordinateRays.exists_smul_of_wedge_zero v w hw hdet
  have hc0 : c ≠ 0 := by
    intro h
    apply hv
    simpa only [h, zero_smul] using hc
  rw [hc]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) w

theorem span_eq_of_nonzero_rankOne_mem_line (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (a : K) (ha : sigma a = a)
    (ha0 : a ≠ 0) (v w : Fin 2 → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (hmem : rankOneParameter sigma hsigma a ha v ∈ rankOneLine sigma hsigma w) :
    (K ∙ v : Submodule K (Fin 2 → K)) = K ∙ w := by
  obtain ⟨b, hb, he⟩ := hmem
  exact span_eq_of_rankOneParameter_eq sigma hsigma a b ha hb ha0 v w hv hw he

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
