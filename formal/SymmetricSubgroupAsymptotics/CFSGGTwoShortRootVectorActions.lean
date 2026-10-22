import SymmetricSubgroupAsymptotics.CFSGGTwoRootUnits
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-! Eight sparse coordinate formulas for each actual short-root unit.
Staging each root action avoids expanding a triple product of dense
matrix entries in the subsequent Weyl-word calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
open CFSGGTwoSerreMatrices
variable {R : Type*} [CommRing R]

def positiveAction (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    ![v (pos 0) + t * v (pos 1), v (pos 1),
      v (pos 2) + t * (v (pos 3) + v (neg 3)) - t ^ 2 * v (neg 2),
      v (pos 3) - t * v (neg 2)]
    ![v (neg 0), v (neg 1) - t * v (neg 0), v (neg 2),
      v (neg 3) - t * v (neg 2)]

def negativeAction (t : R) (v : Index → R) : Index → R :=
  Sum.elim
    ![v (pos 0), v (pos 1) + t * v (pos 0), v (pos 2),
      v (pos 3) + t * v (pos 2)]
    ![v (neg 0) - t * v (neg 1), v (neg 1),
      v (neg 2) - t * (v (pos 3) + v (neg 3)) - t ^ 2 * v (pos 2),
      v (neg 3) + t * v (pos 2)]

theorem positive_apply (t : R) (v : Index → R) :
    (rootTransvection R false 0 t : Mat R) *ᵥ v = positiveAction t v := by
  simp only [rootTransvection_val, rootMatrix, rootSecond, Bool.false_eq_true, if_false,
    positive_zero_explicit, positiveSecond, if_true, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [positiveAction, pos, neg, Function.update_apply,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff] <;> ring

theorem negative_apply (t : R) (v : Index → R) :
    (rootTransvection R true 0 t : Mat R) *ᵥ v = negativeAction t v := by
  simp only [rootTransvection_val, rootMatrix, rootSecond, if_true,
    negative, negativeSecond, positive_zero_explicit, positiveSecond,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_single,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [negativeAction, pos, neg, Function.update_apply,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff] <;> ring

end SymmetricSubgroupAsymptotics.CFSGGTwoShortRootVectorActions
