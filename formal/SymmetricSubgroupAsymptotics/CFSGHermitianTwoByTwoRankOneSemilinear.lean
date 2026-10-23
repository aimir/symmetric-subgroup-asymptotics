import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoConeSemilinear
import Mathlib.Tactic.LinearCombination

/-! The normalized cone formulas act on rank-one POINT VECTORS by an
actual quadratic-field semilinear diagonal map. This converts coefficient
rigidity into the projective-line statement needed by polar gluing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem parameters_eq_axes_offDiagonal (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (A : parameters sigma) :
    A = axis0 sigma (A.val 0 0) (A.property 0 0) + offDiagonalHom sigma hsigma (A.val 0 1) +
      axis1 sigma (A.val 1 1) (A.property 1 1) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [axis0, axis1, offDiagonalHom, Matrix.of_apply]
  exact (A.property 1 0).symm

theorem axis0_image_of_semilinear (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (alpha : K) (halpha : sigma alpha = alpha)
    (haxis : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (a : K) (ha : sigma a = a) :
    E (axis0 sigma a ha) = axis0 sigma (tau a * alpha)
      (by rw [map_mul, automorphism_fixed_of_commute sigma tau hcomm a ha, halpha]) := by
  have hh := hscalar a ha (axis0 sigma 1 (map_one sigma))
  simpa only [fixedScaleHom_axis0, mul_one, haxis] using hh

theorem normalized_cone_entries (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (halpha0 : alpha ≠ 0) (hbeta0 : beta ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta)
    (A : parameters sigma) :
    (E A).val 0 0 = tau (A.val 0 0) * alpha ∧
      (E A).val 0 1 = offDiagonalImageHom sigma hsigma E (A.val 0 1) ∧
      (E A).val 1 1 = tau (A.val 1 1) * beta := by
  have hL := first_diagonal_mixing_zero sigma tau hsigma hcomm E hscalar hcone alpha beta halpha hbeta hbeta0 haxis0 haxis1
  have hM := second_diagonal_mixing_zero sigma tau hsigma hcomm E hscalar hcone alpha beta halpha hbeta halpha0 haxis0 haxis1
  have he := congrArg E (parameters_eq_axes_offDiagonal sigma hsigma A)
  simp only [map_add, axis0_image_of_semilinear sigma tau hcomm E hscalar alpha halpha haxis0,
    axis1_image_of_semilinear sigma tau hcomm E hscalar beta hbeta haxis1] at he
  constructor
  · have h00 := congrArg (fun B : parameters sigma => B.val 0 0) he
    change (E A).val 0 0 = tau (A.val 0 0) * alpha + (E (offDiagonalHom sigma hsigma (A.val 0 1))).val 0 0 + 0 at h00
    simpa only [hL, add_zero] using h00
  · constructor
    · have h01 := congrArg (fun B : parameters sigma => B.val 0 1) he
      change (E A).val 0 1 = 0 + (E (offDiagonalHom sigma hsigma (A.val 0 1))).val 0 1 + 0 at h01
      simpa only [zero_add, add_zero] using h01
    · have h11 := congrArg (fun B : parameters sigma => B.val 1 1) he
      change (E A).val 1 1 = 0 + (E (offDiagonalHom sigma hsigma (A.val 0 1))).val 1 1 + tau (A.val 1 1) * beta at h11
      simpa only [hM, zero_add] using h11

theorem normalized_cone_rankOne_semilinear (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta gamma : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (halpha0 : alpha ≠ 0) (hbeta0 : beta ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta)
    (hgamma : gamma * sigma gamma = alpha * beta)
    (hoff : ∀ x, offDiagonalImageHom sigma hsigma E x = gamma * tau x)
    (a : K) (ha : sigma a = a) (v : Fin 2 → K) :
    E (rankOneParameter sigma hsigma a ha v) =
      rankOneParameter sigma hsigma (tau a / alpha)
        (by rw [map_div₀, automorphism_fixed_of_commute sigma tau hcomm a ha, halpha])
        ![alpha * tau (v 0), sigma gamma * tau (v 1)] := by
  let B := rankOneParameter sigma hsigma a ha v
  have hentries := normalized_cone_entries sigma tau hsigma hcomm E hscalar hcone
    alpha beta halpha hbeta halpha0 hbeta0 haxis0 haxis1 B
  have h00 := hentries.1
  have h01 := hentries.2.1
  have h11 := hentries.2.2
  rw [hoff] at h01
  have h10 : (E B).val 1 0 = sigma (gamma * tau (B.val 0 1)) := by
    rw [← (E B).property 1 0, h01]
  have hsT (x : K) : sigma (tau x) = tau (sigma x) := hcomm x
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · change (E B).val 0 0 = _
    rw [h00]
    change tau (a * v 0 * sigma (v 0)) * alpha =
      (tau a / alpha) * (alpha * tau (v 0)) * sigma (alpha * tau (v 0))
    rw [map_mul, map_mul, map_mul, halpha, hcomm]
    field_simp [halpha0] <;> ring
  · change (E B).val 0 1 = _
    rw [h01]
    change gamma * tau (a * v 0 * sigma (v 1)) =
      (tau a / alpha) * (alpha * tau (v 0)) * sigma (sigma gamma * tau (v 1))
    rw [map_mul, map_mul, map_mul, hsigma, hcomm]
    field_simp [halpha0] <;> ring
  · change (E B).val 1 0 = _
    rw [h10]
    change sigma (gamma * tau (a * v 0 * sigma (v 1))) =
      (tau a / alpha) * (sigma gamma * tau (v 1)) * sigma (alpha * tau (v 0))
    simp only [map_mul, hsT, hsigma, ha, halpha]
    field_simp [halpha0] <;> ring
  · change (E B).val 1 1 = _
    rw [h11]
    change tau (a * v 1 * sigma (v 1)) * beta =
      (tau a / alpha) * (sigma gamma * tau (v 1)) * sigma (sigma gamma * tau (v 1))
    simp only [map_mul, hsigma, hsT]
    field_simp [halpha0]
    linear_combination -(tau a * tau (v 1) * tau (sigma (v 1))) * hgamma

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
