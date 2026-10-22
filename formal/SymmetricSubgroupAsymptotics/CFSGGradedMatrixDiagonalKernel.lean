import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.GroupTheory.Solvable

/-! A grading-preserving matrix fixing its zero-weight columns is diagonal
when every nonzero weight has a unique original coordinate. This is the
literal matrix kernel needed for a lifted Weyl-word argument; it uses no
separation of integer weights inside the coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
variable {I R L : Type*} [Fintype I] [DecidableEq I] [CommRing R] [Zero L]

theorem isDiag_of_preserves_of_fixes_zero (weight : I→L)
    (hsep : ∀i j,weight i=weight j→weight j≠0→i=j)
    (M : Matrix I I R) (hM : Supported weight id M)
    (hfix : ∀j,weight j=0→M*ᵥPi.single j 1=Pi.single j 1) : M.IsDiag := by
  intro i j hij
  by_cases hj : weight j=0
  · have he := congrFun (hfix j hj) i
    simpa [Matrix.mulVec_single_one,hij,Ne.symm hij] using he
  · exact hM i j (fun he=>hij (hsep i j he hj))

theorem commute_of_preserves_of_fixes_zero (weight : I→L)
    (hsep : ∀i j,weight i=weight j→weight j≠0→i=j)
    (M N : Matrix I I R) (hM : Supported weight id M) (hN : Supported weight id N)
    (hfixM : ∀j,weight j=0→M*ᵥPi.single j 1=Pi.single j 1)
    (hfixN : ∀j,weight j=0→N*ᵥPi.single j 1=Pi.single j 1) : M*N=N*M := by
  have hdM := isDiag_of_preserves_of_fixes_zero weight hsep M hM hfixM
  have hdN := isDiag_of_preserves_of_fixes_zero weight hsep N hN hfixN
  rw [←hdM.diagonal_diag,←hdN.diagonal_diag,Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem subgroup_soluble_of_preserves_of_fixes_zero (weight : I→L)
    (hsep : ∀i j,weight i=weight j→weight j≠0→i=j)
    (H : Subgroup ((Matrix I I R)ˣ))
    (hM : ∀g∈H,Supported weight id (g : Matrix I I R))
    (hfix : ∀g∈H,∀j,weight j=0→(g : Matrix I I R)*ᵥPi.single j 1=Pi.single j 1) :
    IsSolvable H := by
  apply isSolvable_of_comm
  intro g h
  apply Subtype.ext
  apply Units.ext
  exact commute_of_preserves_of_fixes_zero weight hsep _ _
    (hM g.val g.property) (hM h.val h.property)
    (hfix g.val g.property) (hfix h.val h.property)

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport
