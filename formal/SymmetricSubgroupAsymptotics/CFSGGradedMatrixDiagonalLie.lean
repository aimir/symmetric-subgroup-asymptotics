import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Ring

/-! Actual diagonal adjoint action on a literal homogeneous lattice
degree. The character is additive into the coefficient ring; no
eigenvalue-separation or matrix-faithfulness premise is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixDiagonalLie
open CFSGGradedMatrixSupport
variable {I V K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [CommRing K]

theorem diagonal_lie_of_supported (weight : I→V) (χ : V→+K) (d : V)
    (M : Matrix I I K) (hM : Supported weight (fun v=>v+d) M) :
    ⁅Matrix.diagonal (fun i=>χ (weight i)),M⁆=χ d • M := by
  apply Matrix.ext
  intro i j
  rw [Ring.lie_def,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.smul_apply,smul_eq_mul]
  by_cases he : weight i=weight j+d
  · rw [he,map_add]
    ring
  · rw [hM i j he]
    ring

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixDiagonalLie
