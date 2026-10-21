import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation

/-! Exact action of a literal coordinate-pair rotation on every
standard basis vector. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
variable (R : Type*) [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

theorem rotation_basis_left (p q : I) (hpq : p ≠ q) :
    rotation R p q *ᵥ Pi.single p 1 = Pi.single q 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [rotation, Matrix.col, Matrix.single, Matrix.one_apply, Pi.single_apply,
    hpq, Ne.symm hpq, eq_comm]

theorem rotation_basis_right (p q : I) (hpq : p ≠ q) :
    rotation R p q *ᵥ Pi.single q 1 = -Pi.single p 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [rotation, Matrix.col, Matrix.single, Matrix.one_apply, Pi.single_apply,
    hpq, Ne.symm hpq, eq_comm]

theorem rotation_basis_other (p q j : I) (hjp : j ≠ p) (hjq : j ≠ q) :
    rotation R p q *ᵥ Pi.single j 1 = Pi.single j 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [rotation, Matrix.col, Matrix.single, Matrix.one_apply, Pi.single_apply,
    hjp, hjq, Ne.symm hjp, Ne.symm hjq, eq_comm]

end SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation
