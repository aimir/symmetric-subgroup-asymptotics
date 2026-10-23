import SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
import Mathlib.Algebra.BigOperators.Fin

/-! Exact vector action of the literal four-entry two-plane shear.
The coordinate pairs need not be injective for the displayed additive
identity. No classical group or rank assumption enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private theorem single_mulVec_eq (p q : I) (a : K) (x : I → K) :
    Matrix.single p q a *ᵥ x = Pi.single p (a * x q) := by
  ext i
  by_cases hi : i = p <;>
    simp [Matrix.single_mulVec, Pi.single_apply, hi]

theorem array_mulVec (p q : Fin 2 → I) (B : Matrix (Fin 2) (Fin 2) K) (x : I → K) :
    array p q B *ᵥ x =
      Pi.single (p 0) (B 0 0 * x (q 0) + B 0 1 * x (q 1)) +
        Pi.single (p 1) (B 1 0 * x (q 0) + B 1 1 * x (q 1)) := by
  simp only [array, Fin.sum_univ_two, Matrix.add_mulVec, single_mulVec_eq]
  ext i
  by_cases hi0 : i = p 0 <;> by_cases hi1 : i = p 1
  all_goals simp only [Pi.add_apply, Pi.single_apply, hi0, hi1, if_true, if_false]
  all_goals (try split_ifs) <;> ring

end SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
