import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoAxes

/-! Uniform no-axis-hit reconstruction for the normalized Hermitian
cone. Semilinearity over the fixed scalars, proved from the centroid,
is used here only to rule out a nonzero diagonal-mixing functional.
There is no small-field exception or division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem axis1_image_of_semilinear (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (beta : K) (hbeta : sigma beta = beta)
    (haxis : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta)
    (a : K) (ha : sigma a = a) :
    E (axis1 sigma a ha) = axis1 sigma (tau a * beta)
      (by rw [map_mul, automorphism_fixed_of_commute sigma tau hcomm a ha, hbeta]) := by
  have hh := hscalar a ha (axis1 sigma 1 (map_one sigma))
  simpa only [fixedScaleHom_axis1, mul_one, haxis] using hh

theorem axis1_surjective_of_semilinear (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (beta : K) (hbeta : sigma beta = beta) (hbeta0 : beta ≠ 0)
    (haxis : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta)
    (d : K) (hd : sigma d = d) :
    ∃ (a : K) (ha : sigma a = a), E (axis1 sigma a ha) = axis1 sigma d hd := by
  have hdiv : sigma (d / beta) = d / beta := by rw [map_div₀, hd, hbeta]
  have ha := automorphism_symm_fixed_of_commute sigma tau hcomm (d / beta) hdiv
  refine ⟨tau.symm (d / beta), ha, ?_⟩
  have hh := axis1_image_of_semilinear sigma tau hcomm E hscalar beta hbeta haxis _ ha
  simpa only [tau.apply_symm_apply, div_mul_cancel₀ d hbeta0] using hh

theorem first_diagonal_mixing_zero (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (hbeta0 : beta ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta) :
    ∀ x, (E (offDiagonalHom sigma hsigma x)).val 0 0 = 0 := by
  let L : K → K := fun x => (E (offDiagonalHom sigma hsigma x)).val 0 0
  have hfixed (x : K) : sigma (L x) = L x := (E (offDiagonalHom sigma hsigma x)).property 0 0
  have hsmul (a : K) (ha : sigma a = a) (x : K) : L (a * x) = tau a * L x := by
    have hh := hscalar a ha (offDiagonalHom sigma hsigma x)
    rw [offDiagonal_scaled] at hh
    exact congrArg (fun A : parameters sigma => A.val 0 0) hh
  have hray00 (x : K) : (E (ray sigma hsigma x)).val 0 0 = alpha + L x := by
    rw [ray_eq_axes_offDiagonal, map_add, map_add, haxis0,
      axis1_image_of_semilinear sigma tau hcomm E hscalar beta hbeta haxis1]
    change alpha + L x + 0 = alpha + L x
    exact add_zero _
  have havoid (x : K) : alpha + L x ≠ 0 := by
    intro hz
    have hd : (ray sigma hsigma x).val.det = 0 := by
      rw [ray_eq_rankOne]
      exact rankOne_det sigma 1 ![1, sigma x]
    have h00 : (E (ray sigma hsigma x)).val 0 0 = 0 := (hray00 x).trans hz
    have hline := eq_axis1_of_det_zero_of_first_diagonal sigma (E (ray sigma hsigma x))
      (hcone (ray sigma hsigma x) hd) h00
    obtain ⟨a, ha, hea⟩ := axis1_surjective_of_semilinear sigma tau hcomm E hscalar beta hbeta hbeta0 haxis1
      ((E (ray sigma hsigma x)).val 1 1) ((E (ray sigma hsigma x)).property 1 1)
    have he : ray sigma hsigma x = axis1 sigma a ha := E.injective (hline.trans hea.symm)
    have hentry := congrArg (fun A : parameters sigma => A.val 0 0) he
    exact one_ne_zero (show (1 : K) = 0 from hentry)
  exact zero_of_fixed_semilinear_avoids sigma tau hcomm alpha halpha L hfixed hsmul havoid

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
