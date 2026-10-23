import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRays

/-! Fixed scalars on the actual additive Hermitian coefficient carrier.
No linear structure over a supplied field is imposed on an automorphism:
these are literal scalar endomorphisms whose common centroid will be
recovered from the rank-one root lines. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def fixedScaleHom (sigma : K ≃+* K) (a : K) (ha : sigma a = a) :
    parameters sigma →+ parameters sigma where
  toFun A := ⟨a • A.val, by
    intro i j
    change sigma (a * A.val j i) = a * A.val i j
    rw [map_mul, ha, A.property i j]⟩
  map_zero' := by apply Subtype.ext; exact smul_zero a
  map_add' A B := by apply Subtype.ext; exact smul_add a A.val B.val

theorem fixedScaleHom_entry (sigma : K ≃+* K) (a : K) (ha : sigma a = a)
    (A : parameters sigma) (i j : Fin 2) :
    (fixedScaleHom sigma a ha A).val i j = a * A.val i j := rfl

theorem fixedScaleHom_one (sigma : K ≃+* K) (A : parameters sigma) :
    fixedScaleHom sigma 1 (map_one sigma) A = A := by
  apply Subtype.ext
  exact one_smul K A.val

theorem fixedScaleHom_mul (sigma : K ≃+* K) (a b : K)
    (ha : sigma a = a) (hb : sigma b = b) (A : parameters sigma) :
    fixedScaleHom sigma a ha (fixedScaleHom sigma b hb A) =
      fixedScaleHom sigma (a * b) (by rw [map_mul, ha, hb]) A := by
  apply Subtype.ext
  exact smul_smul a b A.val

theorem fixedScaleHom_axis0 (sigma : K ≃+* K) (a b : K)
    (ha : sigma a = a) (hb : sigma b = b) :
    fixedScaleHom sigma a ha (axis0 sigma b hb) =
      axis0 sigma (a * b) (by rw [map_mul, ha, hb]) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedScaleHom, axis0, Matrix.of_apply]

theorem fixedScaleHom_axis1 (sigma : K ≃+* K) (a b : K)
    (ha : sigma a = a) (hb : sigma b = b) :
    fixedScaleHom sigma a ha (axis1 sigma b hb) =
      axis1 sigma (a * b) (by rw [map_mul, ha, hb]) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedScaleHom, axis1, Matrix.of_apply]

theorem fixedScaleHom_ray (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (a : K) (ha : sigma a = a) (x : K) :
    fixedScaleHom sigma a ha (ray sigma hsigma x) =
      rankOneParameter sigma hsigma a ha ![1, sigma x] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedScaleHom, ray, rankOneParameter, rankOne, Matrix.of_apply, hsigma,
      mul_comm] <;> ring

theorem axis0_eq_scaled_ray_zero (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (a : K) (ha : sigma a = a) :
    axis0 sigma a ha = fixedScaleHom sigma a ha (ray sigma hsigma 0) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedScaleHom, ray, axis0, Matrix.of_apply, map_zero]

theorem axis1_eq_rankOne (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (a : K) (ha : sigma a = a) :
    axis1 sigma a ha = rankOneParameter sigma hsigma a ha ![0, 1] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axis1, rankOneParameter, rankOne, Matrix.of_apply]

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
