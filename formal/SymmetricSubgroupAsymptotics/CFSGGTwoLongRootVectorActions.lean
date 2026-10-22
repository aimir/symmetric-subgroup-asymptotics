import SymmetricSubgroupAsymptotics.CFSGGTwoRootUnits
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-! Sparse coordinates of the actual long simple-root unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGGTwoLongRootVectorActions
open CFSGGTwoSerreMatrices
variable {R : Type*} [CommRing R]

def positiveAction (t : R) (v : Index → R) : Index → R :=
  Sum.elim ![v (pos 0), v (pos 1) + t * v (pos 2), v (pos 2), v (pos 3)]
    ![v (neg 0), v (neg 1), v (neg 2) - t * v (neg 1), v (neg 3)]

theorem positive_apply (t : R) (v : Index → R) :
    (rootTransvection R false 1 t : Mat R) *ᵥ v = positiveAction t v := by
  simp only [rootTransvection_val, rootMatrix, rootSecond, Bool.false_eq_true, if_false,
    positive_one_explicit, positiveSecond, if_neg (show (1 : Fin 2) ≠ 0 by decide),
    smul_zero, add_zero, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [positiveAction, pos, neg, Function.update_apply,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Fin.ext_iff] <;> ring

end SymmetricSubgroupAsymptotics.CFSGGTwoLongRootVectorActions
