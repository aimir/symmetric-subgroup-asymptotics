import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStandardSingularSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Exact coordinates and dimension of the literal standard singular
space. The index floor((r+1)/2) is derived from the displayed support
condition, with no unitary Witt-index assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

def unitaryStandardCoordinateEquiv (q : CFSG.PrimePower) (r : ℕ) :
    (Fin ((r + 1) / 2) → q.Extension 2) ≃ₗ[q.Extension 2] unitaryStandardSingularSpace q r where
  toFun v := ⟨fun j => if h : j.val < (r + 1) / 2 then v ⟨j.val, h⟩ else 0, by
    intro j hj
    have hn : ¬j.val < (r + 1) / 2 := by omega
    exact dif_neg hn⟩
  invFun x := fun i => x.val ⟨i.val, by have hi := i.isLt; omega⟩
  left_inv v := by
    ext i
    dsimp only
    rw [dif_pos i.isLt]
  right_inv x := by
    apply Subtype.ext
    funext j
    dsimp only
    by_cases hj : j.val < (r + 1) / 2
    · rw [dif_pos hj]
    · rw [dif_neg hj]
      exact (x.property j (by omega)).symm
  map_add' v w := by
    apply Subtype.ext
    funext j
    change (if h : j.val < (r + 1) / 2 then (v + w) ⟨j.val, h⟩ else 0) =
      (if h : j.val < (r + 1) / 2 then v ⟨j.val, h⟩ else 0) +
      (if h : j.val < (r + 1) / 2 then w ⟨j.val, h⟩ else 0)
    by_cases hj : j.val < (r + 1) / 2
    · simp only [dif_pos hj, Pi.add_apply]
    · simp only [dif_neg hj, Pi.add_apply, add_zero]
  map_smul' a v := by
    apply Subtype.ext
    funext j
    change (if h : j.val < (r + 1) / 2 then (a • v) ⟨j.val, h⟩ else 0) =
      a • (if h : j.val < (r + 1) / 2 then v ⟨j.val, h⟩ else 0)
    by_cases hj : j.val < (r + 1) / 2
    · simp only [dif_pos hj, Pi.smul_apply]
    · simp only [dif_neg hj, Pi.smul_apply, smul_zero]

theorem unitaryStandardSingularSpace_finrank (q : CFSG.PrimePower) (r : ℕ) :
    Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q r) = (r + 1) / 2 := by
  rw [← (unitaryStandardCoordinateEquiv q r).finrank_eq]
  simp

theorem unitaryStandardSingularSpace_finrank_ge_three (q : CFSG.PrimePower)
    (r : ℕ) (hr : 5 ≤ r) :
    3 ≤ Module.finrank (q.Extension 2) (unitaryStandardSingularSpace q r) := by
  rw [unitaryStandardSingularSpace_finrank]
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
