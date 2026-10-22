import SymmetricSubgroupAsymptotics.CFSGStrictUpperNilpotence
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.GroupTheory.PGroup

/-! Actual upper triangular and unitriangular subgroups of matrix
units in an explicitly specified complete coordinate flag. The
unipotent p-group proof is strict-upper nilpotence after the SAME
coordinate reindexing. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K] {m : ℕ}

private theorem upper_inverse (e : I ≃ Fin m) (A : (Matrix I I K)ˣ)
    (hA : (A : Matrix I I K).BlockTriangular e) :
    (↑(A⁻¹) : Matrix I I K).BlockTriangular e := by
  letI matrixFlag_invertible : Invertible (A : Matrix I I K) := A.invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hi : (A : Matrix I I K)⁻¹ = (↑(A⁻¹) : Matrix I I K) :=
    Matrix.inv_eq_left_inv (Units.inv_mul A)
  rwa [hi] at h

theorem upper_diag_mul (e : I ≃ Fin m) {A B : Matrix I I K}
    (hA : A.BlockTriangular e) (hB : B.BlockTriangular e) (i : I) :
    (A * B) i i = A i i * B i i := by
  change (∑ k, A i k * B k i) = _
  apply Finset.sum_eq_single i
  · intro k _ hki
    have hne : e k ≠ e i := e.injective.ne hki
    rcases lt_or_gt_of_ne hne with hk | hk
    · rw [hA hk, zero_mul]
    · rw [hB hk, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

def borelUnits (e : I ≃ Fin m) : Subgroup ((Matrix I I K)ˣ) where
  carrier := {A | (A : Matrix I I K).BlockTriangular e}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun hA hB => hA.mul hB
  inv_mem' := fun hA => upper_inverse e _ hA

def unipotentUnits (e : I ≃ Fin m) : Subgroup ((Matrix I I K)ˣ) where
  carrier := {A | (A : Matrix I I K).BlockTriangular e ∧ ∀ i, (A : Matrix I I K) i i = 1}
  one_mem' := ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  mul_mem' := by
    intro A B hA hB
    refine ⟨hA.1.mul hB.1, fun i => ?_⟩
    change ((A : Matrix I I K) * (B : Matrix I I K)) i i = 1
    rw [upper_diag_mul e hA.1 hB.1, hA.2, hB.2, one_mul]
  inv_mem' := by
    intro A hA
    have hi := upper_inverse e A hA.1
    refine ⟨hi, fun i => ?_⟩
    have h := congrArg (fun M : Matrix I I K => M i i) (Units.inv_mul A)
    dsimp only at h
    simp only [Matrix.one_apply_eq] at h
    change ((↑(A⁻¹) : Matrix I I K) * (A : Matrix I I K)) i i = 1 at h
    rw [upper_diag_mul e hi hA.1, hA.2, mul_one] at h
    exact h

theorem unipotentUnits_le_borelUnits (e : I ≃ Fin m) :
    (unipotentUnits e : Subgroup ((Matrix I I K)ˣ)) ≤ borelUnits e := fun _ h => h.1

theorem unipotentUnits_isPGroup (e : I ≃ Fin m) (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (unipotentUnits e : Subgroup ((Matrix I I K)ˣ)) := by
  cases m with
  | zero =>
    intro A
    refine ⟨0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact Fin.elim0 (e i)
  | succ m =>
    intro A
    let M : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
      Matrix.reindexAlgEquiv K K e (A.val : Matrix I I K)
    have hM : M.BlockTriangular id := by
      intro i j hij
      change (A.val : Matrix I I K) (e.symm i) (e.symm j) = 0
      apply A.property.1
      simpa only [Equiv.apply_symm_apply] using hij
    have hdiag : ∀ i, M i i = 1 := fun i => A.property.2 (e.symm i)
    have hp := CFSGStrictUpperNilpotence.unitriangular_pow_prime_pow M hM hdiag (p := p)
    refine ⟨m + 1, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply (Matrix.reindexAlgEquiv K K e).injective
    change Matrix.reindexAlgEquiv K K e ((A.val : Matrix I I K) ^ (p ^ (m + 1))) =
      Matrix.reindexAlgEquiv K K e 1
    simpa only [map_pow, map_one] using hp

end SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
