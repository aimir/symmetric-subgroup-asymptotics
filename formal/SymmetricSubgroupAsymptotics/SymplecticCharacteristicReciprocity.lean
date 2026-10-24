import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! Actual symplectic matrices have the same characteristic polynomial
as their inverse. In characteristic two their determinant is one and
the characteristic polynomial is literally self-reciprocal. This is a
matrix identity, not a conjugacy-class or module-type assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.SymplecticCharacteristicReciprocity
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem charpoly_inverse_eq (A : Matrix.symplecticGroup I K) :
    ((A⁻¹ : Matrix.symplecticGroup I K) : Matrix (I⊕I) (I⊕I) K).charpoly =
      (A : Matrix (I⊕I) (I⊕I) K).charpoly := by
  rw [_root_.SymplecticGroup.coe_inv]
  calc
    _ = (Matrix.J I K * ((-Matrix.J I K) *
        (A : Matrix (I⊕I) (I⊕I) K).transpose)).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = (A : Matrix (I⊕I) (I⊕I) K).transpose.charpoly := by
      rw [←Matrix.mul_assoc,Matrix.mul_neg,Matrix.J_squared,neg_neg,Matrix.one_mul]
    _ = _ := Matrix.charpoly_transpose _

theorem det_eq_one [CharP K 2] (A : Matrix.symplecticGroup I K) :
    (A : Matrix (I⊕I) (I⊕I) K).det=1 := by
  have h := congrArg Matrix.det (_root_.SymplecticGroup.mem_iff.mp A.property)
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose] at h
  have hs : (A : Matrix (I⊕I) (I⊕I) K).det *
      (A : Matrix (I⊕I) (I⊕I) K).det=1 :=
    (Matrix.isUnit_det_J I K).mul_left_cancel (by
      calc
        _ = (A : Matrix (I⊕I) (I⊕I) K).det * (Matrix.J I K).det *
          (A : Matrix (I⊕I) (I⊕I) K).det := by ring
        _ = (Matrix.J I K).det := h
        _ = _ := (mul_one _).symm)
  have hz : ((A : Matrix (I⊕I) (I⊕I) K).det+1)^2=0 := by
    rw [CharTwo.add_sq,pow_two,hs,one_pow,CharTwo.add_self_eq_zero]
  exact CharTwo.add_eq_zero.mp ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp hz)

theorem charpoly_reverse [CharP K 2] (A : Matrix.symplecticGroup I K) :
    (A : Matrix (I⊕I) (I⊕I) K).charpoly.reverse =
      (A : Matrix (I⊕I) (I⊕I) K).charpoly := by
  have h := Matrix.charpoly_inv (A : Matrix (I⊕I) (I⊕I) K)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (_root_.SymplecticGroup.symplectic_det A.property))
  have hi : ((A : Matrix (I⊕I) (I⊕I) K)⁻¹).charpoly =
      (A : Matrix (I⊕I) (I⊕I) K).charpoly := by
    rw [←_root_.SymplecticGroup.coe_inv']
    exact charpoly_inverse_eq A
  apply Eq.symm
  apply hi.symm.trans
  simpa [←Matrix.reverse_charpoly,det_eq_one A,CharTwo.neg_eq] using h

end SymmetricSubgroupAsymptotics.SymplecticCharacteristicReciprocity
