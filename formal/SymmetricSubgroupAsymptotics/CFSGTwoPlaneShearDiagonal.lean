import SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays

/-! The actual disjoint-coordinate shear has zero displacement on every
diagonal entry. This eliminates projective scalar ambiguity directly,
without a characteristic assumption or a group-order argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem array_diagonal (p q : Fin 2 → I) (hdisj : ∀ i j, q i ≠ p j)
    (B : Matrix (Fin 2) (Fin 2) K) (k : I) : array p q B k k = 0 := by
  simp only [array, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [Matrix.single_apply]
  split_ifs with h
  · exact False.elim (hdisj j i (h.2.trans h.1.symm))
  · rfl

theorem unit_diagonal (p q : Fin 2 → I) (hdisj : ∀ i j, q i ≠ p j)
    (B : Matrix (Fin 2) (Fin 2) K) (k : I) :
    (unit p q hdisj B : Matrix I I K) k k = 1 := by
  change (1 + array p q B) k k = 1
  rw [Matrix.add_apply, Matrix.one_apply_eq, array_diagonal p q hdisj, add_zero]

end SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays
