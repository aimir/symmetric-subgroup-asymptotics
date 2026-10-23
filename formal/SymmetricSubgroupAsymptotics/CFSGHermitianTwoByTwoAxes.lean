import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoScalars

/-! Exact diagonal/off-diagonal coordinates and the all-characteristic
no-axis-hit rigidity step for Hermitian rank-one cone reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def offDiagonalHom (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x) :
    K →+ parameters sigma where
  toFun x := ⟨!![0, x; sigma x, 0], by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Hermitian, Matrix.of_apply, hsigma]⟩
  map_zero' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply, map_add]

theorem offDiagonal_scaled (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (a : K) (ha : sigma a = a) (x : K) :
    fixedScaleHom sigma a ha (offDiagonalHom sigma hsigma x) =
      offDiagonalHom sigma hsigma (a * x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedScaleHom, offDiagonalHom, Matrix.of_apply, map_mul, ha]

theorem ray_eq_axes_offDiagonal (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x) (x : K) :
    ray sigma hsigma x = axis0 sigma 1 (map_one sigma) + offDiagonalHom sigma hsigma x +
      axis1 sigma (x * sigma x) (norm_fixed sigma hsigma x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ray, axis0, axis1, offDiagonalHom, Matrix.of_apply]

theorem eq_axis1_of_det_zero_of_first_diagonal (sigma : K ≃+* K) (A : parameters sigma)
    (hdet : A.val.det = 0) (h00 : A.val 0 0 = 0) :
    A = axis1 sigma (A.val 1 1) (A.property 1 1) := by
  have hp : A.val 0 1 * sigma (A.val 0 1) = 0 := by
    rw [Matrix.det_fin_two, h00, zero_mul, zero_sub, ← A.property 1 0] at hdet
    exact neg_eq_zero.mp hdet
  have h01 : A.val 0 1 = 0 := by
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · exact sigma.injective (h.trans (map_zero sigma).symm)
  have h10 : A.val 1 0 = 0 := by rw [← A.property 1 0, h01, map_zero]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · rfl

theorem automorphism_fixed_of_commute (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (a : K) (ha : sigma a = a) :
    sigma (tau a) = tau a := by rw [hcomm a, ha]

theorem automorphism_symm_fixed_of_commute (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (a : K) (ha : sigma a = a) :
    sigma (tau.symm a) = tau.symm a := by
  apply tau.injective
  calc
    tau (sigma (tau.symm a)) = sigma a := by
      simpa only [tau.apply_symm_apply] using (hcomm (tau.symm a)).symm
    _ = tau (tau.symm a) := by rw [ha, tau.apply_symm_apply]

theorem zero_of_fixed_semilinear_avoids (sigma tau : K ≃+* K)
    (hcomm : Function.Commute sigma tau) (alpha : K) (halpha : sigma alpha = alpha)
    (L : K → K) (hfixed : ∀ x, sigma (L x) = L x)
    (hsmul : ∀ (a : K) (ha : sigma a = a) (x : K), L (a * x) = tau a * L x)
    (havoid : ∀ x, alpha + L x ≠ 0) : ∀ x, L x = 0 := by
  intro x
  by_contra hx
  let z : K := -alpha / L x
  have hz : sigma z = z := by
    dsimp only [z]
    rw [map_div₀, map_neg, halpha, hfixed]
  have ha := automorphism_symm_fixed_of_commute sigma tau hcomm z hz
  have hh := havoid (tau.symm z * x)
  rw [hsmul (tau.symm z) ha x, tau.apply_symm_apply] at hh
  apply hh
  change alpha + (-alpha / L x) * L x = 0
  rw [div_mul_cancel₀ (-alpha) hx, add_neg_cancel]

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
