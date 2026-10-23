import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoAxisRigidity
import SymmetricSubgroupAsymptotics.CFSGQuadraticNormAdditiveRigidity

/-! Normalized all-characteristic Hermitian cone reconstruction. The
second diagonal-mixing term vanishes by exact axis exchange. The
remaining additive off-diagonal map is a norm semisimilitude, hence is
multiplication followed by the actual extension automorphism or its
composition with the involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

private def swapAxes (sigma : K ≃+* K) : parameters sigma ≃+ parameters sigma where
  toFun A := ⟨fun i j => A.val i.rev j.rev, fun i j => A.property i.rev j.rev⟩
  invFun A := ⟨fun i j => A.val i.rev j.rev, fun i j => A.property i.rev j.rev⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    change A.val i.rev.rev j.rev.rev = A.val i j
    simp only [Fin.rev_rev]
  right_inv A := by
    apply Subtype.ext
    ext i j
    change A.val i.rev.rev j.rev.rev = A.val i j
    simp only [Fin.rev_rev]
  map_add' A B := by apply Subtype.ext; ext i j; rfl

private theorem swapAxes_axis0 (sigma : K ≃+* K) (a : K) (ha : sigma a = a) :
    swapAxes sigma (axis0 sigma a ha) = axis1 sigma a ha := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem swapAxes_axis1 (sigma : K ≃+* K) (a : K) (ha : sigma a = a) :
    swapAxes sigma (axis1 sigma a ha) = axis0 sigma a ha := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem swapAxes_scaled (sigma : K ≃+* K) (a : K) (ha : sigma a = a) (A : parameters sigma) :
    swapAxes sigma (fixedScaleHom sigma a ha A) = fixedScaleHom sigma a ha (swapAxes sigma A) := by
  apply Subtype.ext
  ext i j
  rfl

private theorem swapAxes_det (sigma : K ≃+* K) (A : parameters sigma) :
    (swapAxes sigma A).val.det = A.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  change A.val 1 1 * A.val 0 0 - A.val 1 0 * A.val 0 1 =
    A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0
  ring

private theorem swapAxes_offDiagonal (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x) (x : K) :
    swapAxes sigma (offDiagonalHom sigma hsigma x) = offDiagonalHom sigma hsigma (sigma x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapAxes, offDiagonalHom, Matrix.of_apply, Fin.rev, hsigma]

theorem second_diagonal_mixing_zero (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (halpha0 : alpha ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta) :
    ∀ x, (E (offDiagonalHom sigma hsigma x)).val 1 1 = 0 := by
  let F : parameters sigma ≃+ parameters sigma := ((swapAxes sigma).trans E).trans (swapAxes sigma)
  have hs (a : K) (ha : sigma a = a) (A : parameters sigma) :
      F (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (F A) := by
    change swapAxes sigma (E (swapAxes sigma (fixedScaleHom sigma a ha A))) =
      fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha)
        (swapAxes sigma (E (swapAxes sigma A)))
    rw [swapAxes_scaled, hscalar, swapAxes_scaled]
  have hc (A : parameters sigma) (hA : A.val.det = 0) : (F A).val.det = 0 := by
    change (swapAxes sigma (E (swapAxes sigma A))).val.det = 0
    rw [swapAxes_det]
    exact hcone _ ((swapAxes_det sigma A).trans hA)
  have h0 : F (axis0 sigma 1 (map_one sigma)) = axis0 sigma beta hbeta := by
    change swapAxes sigma (E (swapAxes sigma (axis0 sigma 1 (map_one sigma)))) = _
    rw [swapAxes_axis0, haxis1, swapAxes_axis1]
  have h1 : F (axis1 sigma 1 (map_one sigma)) = axis1 sigma alpha halpha := by
    change swapAxes sigma (E (swapAxes sigma (axis1 sigma 1 (map_one sigma)))) = _
    rw [swapAxes_axis1, haxis0, swapAxes_axis0]
  have hh := first_diagonal_mixing_zero sigma tau hsigma hcomm F hs hc beta alpha hbeta halpha halpha0 h0 h1
  intro x
  have hx := hh (sigma x)
  change (E (swapAxes sigma (offDiagonalHom sigma hsigma (sigma x)))).val 1 1 = 0 at hx
  rw [swapAxes_offDiagonal, hsigma] at hx
  exact hx

def offDiagonalImageHom (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (E : parameters sigma ≃+ parameters sigma) : K →+ K where
  toFun x := (E (offDiagonalHom sigma hsigma x)).val 0 1
  map_zero' := by
    exact congrArg (fun A : parameters sigma => A.val 0 1)
      ((congrArg E (map_zero (offDiagonalHom sigma hsigma))).trans (map_zero E))
  map_add' x y := by
    exact congrArg (fun A : parameters sigma => A.val 0 1)
      ((congrArg E (map_add (offDiagonalHom sigma hsigma) x y)).trans
        (map_add E (offDiagonalHom sigma hsigma x) (offDiagonalHom sigma hsigma y)))

theorem normalized_cone_offDiagonal_norm (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (halpha0 : alpha ≠ 0) (hbeta0 : beta ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta) (x : K) :
    CFSGQuadraticNormAdditiveRigidity.norm sigma (offDiagonalImageHom sigma hsigma E x) =
      (alpha * beta) * tau (CFSGQuadraticNormAdditiveRigidity.norm sigma x) := by
  have hL := first_diagonal_mixing_zero sigma tau hsigma hcomm E hscalar hcone alpha beta halpha hbeta hbeta0 haxis0 haxis1
  have hM := second_diagonal_mixing_zero sigma tau hsigma hcomm E hscalar hcone alpha beta halpha hbeta halpha0 haxis0 haxis1
  have h00 : (E (ray sigma hsigma x)).val 0 0 = alpha := by
    rw [ray_eq_axes_offDiagonal, map_add, map_add, haxis0,
      axis1_image_of_semilinear sigma tau hcomm E hscalar beta hbeta haxis1]
    change alpha + (E (offDiagonalHom sigma hsigma x)).val 0 0 + 0 = alpha
    simp only [hL, add_zero]
  have h11 : (E (ray sigma hsigma x)).val 1 1 = beta * tau (x * sigma x) := by
    rw [ray_eq_axes_offDiagonal, map_add, map_add, haxis0,
      axis1_image_of_semilinear sigma tau hcomm E hscalar beta hbeta haxis1]
    change 0 + (E (offDiagonalHom sigma hsigma x)).val 1 1 + tau (x * sigma x) * beta = _
    simp only [hM, zero_add]
    exact mul_comm _ _
  have h01 : (E (ray sigma hsigma x)).val 0 1 = offDiagonalImageHom sigma hsigma E x := by
    rw [ray_eq_axes_offDiagonal, map_add, map_add, haxis0,
      axis1_image_of_semilinear sigma tau hcomm E hscalar beta hbeta haxis1]
    change 0 + (E (offDiagonalHom sigma hsigma x)).val 0 1 + 0 =
      (E (offDiagonalHom sigma hsigma x)).val 0 1
    simp only [zero_add, add_zero]
  have hd : (ray sigma hsigma x).val.det = 0 := by rw [ray_eq_rankOne]; exact rankOne_det sigma 1 _
  have hh := hcone (ray sigma hsigma x) hd
  rw [Matrix.det_fin_two, ← (E (ray sigma hsigma x)).property 1 0, h00, h11, h01] at hh
  change offDiagonalImageHom sigma hsigma E x * sigma (offDiagonalImageHom sigma hsigma E x) = _
  calc
    _ = alpha * (beta * tau (x * sigma x)) := (sub_eq_zero.mp hh).symm
    _ = _ := by change _ = (alpha * beta) * tau (x * sigma x); ring

theorem normalized_cone_offDiagonal_semilinear (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (halpha0 : alpha ≠ 0) (hbeta0 : beta ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta) :
    (∀ x, offDiagonalImageHom sigma hsigma E x = offDiagonalImageHom sigma hsigma E 1 * tau x) ∨
      (∀ x, offDiagonalImageHom sigma hsigma E x = offDiagonalImageHom sigma hsigma E 1 * tau (sigma x)) := by
  exact CFSGQuadraticNormAdditiveRigidity.semilinearSimilitude_eq_mul_or_mul_sigma sigma tau hcomm
    (offDiagonalImageHom sigma hsigma E) (alpha * beta) (mul_ne_zero halpha0 hbeta0)
    (normalized_cone_offDiagonal_norm sigma tau hsigma hcomm E hscalar hcone alpha beta
      halpha hbeta halpha0 hbeta0 haxis0 haxis1)

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
