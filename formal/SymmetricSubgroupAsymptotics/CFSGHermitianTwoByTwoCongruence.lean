import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoScalars
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing

/-! Literal invertible Hermitian congruence as an auxiliary coordinate
change. This is generic matrix algebra, not an assertion that an
arbitrary GL2 element lies in the original unitary group. It preserves
the actual Hermitian cone, fixed scalars and rank-one vector labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def coefficientAdjoint (sigma : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  (A.map sigma).transpose

theorem coefficientAdjoint_mul (sigma : K ≃+* K) (A B : Matrix (Fin 2) (Fin 2) K) :
    coefficientAdjoint sigma (A * B) = coefficientAdjoint sigma B * coefficientAdjoint sigma A := by
  simp only [coefficientAdjoint, Matrix.map_mul, Matrix.transpose_mul]

theorem coefficientAdjoint_twice (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (A : Matrix (Fin 2) (Fin 2) K) : coefficientAdjoint sigma (coefficientAdjoint sigma A) = A := by
  ext i j
  exact hsigma (A i j)

theorem coefficientAdjoint_one (sigma : K ≃+* K) :
    coefficientAdjoint sigma (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [coefficientAdjoint, Matrix.one_apply, hij, eq_comm]

private theorem congruence_hermitian (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (D : Matrix (Fin 2) (Fin 2) K) (A : parameters sigma) :
    Hermitian sigma (D * A.val * coefficientAdjoint sigma D) := by
  have hA : coefficientAdjoint sigma A.val = A.val := by
    ext i j
    exact A.property i j
  have hh : coefficientAdjoint sigma (D * A.val * coefficientAdjoint sigma D) =
      D * A.val * coefficientAdjoint sigma D := by
    rw [coefficientAdjoint_mul, coefficientAdjoint_mul, coefficientAdjoint_twice sigma hsigma, hA]
    exact (mul_assoc _ _ _).symm
  intro i j
  exact congrFun (congrFun hh i) j

private def congruenceHom (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (D : Matrix (Fin 2) (Fin 2) K) : parameters sigma →+ parameters sigma where
  toFun A := ⟨D * A.val * coefficientAdjoint sigma D, congruence_hermitian sigma hsigma D A⟩
  map_zero' := by
    apply Subtype.ext
    change D * 0 * coefficientAdjoint sigma D = 0
    rw [mul_zero, zero_mul]
  map_add' A B := by
    apply Subtype.ext
    change D * (A.val + B.val) * coefficientAdjoint sigma D =
      D * A.val * coefficientAdjoint sigma D + D * B.val * coefficientAdjoint sigma D
    rw [mul_add, add_mul]

def coefficientCongruence (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (D : (Matrix (Fin 2) (Fin 2) K)ˣ) : parameters sigma ≃+ parameters sigma where
  toFun := congruenceHom sigma hsigma D.val
  invFun := congruenceHom sigma hsigma (D⁻¹).val
  left_inv A := by
    apply Subtype.ext
    change (D⁻¹).val * (D.val * A.val * coefficientAdjoint sigma D.val) *
      coefficientAdjoint sigma (D⁻¹).val = A.val
    have hi : (D⁻¹).val * D.val = 1 := D.inv_val
    have hs : coefficientAdjoint sigma D.val * coefficientAdjoint sigma (D⁻¹).val = 1 := by
      have hh := congrArg (coefficientAdjoint sigma) hi
      simpa only [coefficientAdjoint_mul, coefficientAdjoint_one] using hh
    calc
      _ = ((D⁻¹).val * D.val) * A.val *
        (coefficientAdjoint sigma D.val * coefficientAdjoint sigma (D⁻¹).val) := by noncomm_ring
      _ = A.val := by rw [hi, hs, one_mul, mul_one]
  right_inv A := by
    apply Subtype.ext
    change D.val * ((D⁻¹).val * A.val * coefficientAdjoint sigma (D⁻¹).val) *
      coefficientAdjoint sigma D.val = A.val
    have hi : D.val * (D⁻¹).val = 1 := D.val_inv
    have hs : coefficientAdjoint sigma (D⁻¹).val * coefficientAdjoint sigma D.val = 1 := by
      have hh := congrArg (coefficientAdjoint sigma) hi
      simpa only [coefficientAdjoint_mul, coefficientAdjoint_one] using hh
    calc
      _ = (D.val * (D⁻¹).val) * A.val *
        (coefficientAdjoint sigma (D⁻¹).val * coefficientAdjoint sigma D.val) := by noncomm_ring
      _ = A.val := by rw [hi, hs, one_mul, mul_one]
  map_add' A B := map_add (congruenceHom sigma hsigma D.val) A B

theorem coefficientCongruence_fixedScale (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (D : (Matrix (Fin 2) (Fin 2) K)ˣ) (a : K) (ha : sigma a = a) (A : parameters sigma) :
    coefficientCongruence sigma hsigma D (fixedScaleHom sigma a ha A) =
      fixedScaleHom sigma a ha (coefficientCongruence sigma hsigma D A) := by
  apply Subtype.ext
  change D.val * (a • A.val) * coefficientAdjoint sigma D.val =
    a • (D.val * A.val * coefficientAdjoint sigma D.val)
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem coefficientCongruence_det_zero (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (D : (Matrix (Fin 2) (Fin 2) K)ˣ) (A : parameters sigma) (hA : A.val.det = 0) :
    (coefficientCongruence sigma hsigma D A).val.det = 0 := by
  change (D.val * A.val * coefficientAdjoint sigma D.val).det = 0
  rw [Matrix.det_mul, Matrix.det_mul, hA, mul_zero, zero_mul]

theorem coefficientCongruence_rankOne (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (D : (Matrix (Fin 2) (Fin 2) K)ˣ) (a : K) (ha : sigma a = a) (v : Fin 2 → K) :
    coefficientCongruence sigma hsigma D (rankOneParameter sigma hsigma a ha v) =
      rankOneParameter sigma hsigma a ha (D.val *ᵥ v) := by
  apply Subtype.ext
  ext i j
  change (D.val * rankOne sigma a v * coefficientAdjoint sigma D.val) i j =
    a * (D.val *ᵥ v) i * sigma ((D.val *ᵥ v) j)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, rankOne, coefficientAdjoint,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.mulVec, dotProduct, map_add, map_mul]
  ring

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
