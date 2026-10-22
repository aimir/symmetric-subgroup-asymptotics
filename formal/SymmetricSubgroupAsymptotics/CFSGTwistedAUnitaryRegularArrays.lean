import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperMiddleArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

/-! Complete adjacent nonvanishing for an actual three-block upper
array. The proof keeps the same coordinates and the actual middle
matrix; no regular-unipotent existence premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays

theorem vecMul_zero_of_upper {K : Type*} [Field K] (s : ℕ)
    (A : Mat K s) (hA : A.BlockTriangular id) (hd : ∀ i, A i i = 1)
    (w : Fin (s + 1) → K) : (w ᵥ* A) 0 = w 0 := by
  rw [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single 0]
  · change w 0 * A 0 0 = w 0
    rw [hd, mul_one]
  · intro i _ hi
    have hz : A i 0 = 0 := hA (Fin.pos_iff_ne_zero.mpr hi)
    rw [hz, mul_zero]
  · simp

theorem upperMiddleArray_regular {K : Type*} [Field K] (s : ℕ)
    (A : Mat K s) (w v : Fin (s + 1) → K) (b : K)
    (hw : w 0 ≠ 0) (hv : v (Fin.last s) ≠ 0)
    (hA : ∀ i : Fin s, A i.castSucc i.succ ≠ 0) :
    ∀ i : Fin (s + 2),
      (Matrix.reindex (splitEquiv s) (splitEquiv s) (upperMiddleArray w A v b))
        i.castSucc i.succ ≠ 0 := by
  intro i
  by_cases hi0 : i.val = 0
  · have hi : i.castSucc = splitEquiv s (.inl ()) := Fin.ext hi0
    have hj : i.succ = splitEquiv s (.inr (.inl 0)) := by
      apply Fin.ext
      change i.val + 1 = 0 + 1
      omega
    rw [hi, hj]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      upperMiddleArray] using hw
  · by_cases hil : i.val = s + 1
    · have hi : i.castSucc = splitEquiv s (.inr (.inl (Fin.last s))) := by
        apply Fin.ext
        change i.val = s + 1
        exact hil
      have hj : i.succ = splitEquiv s (.inr (.inr ())) := by
        apply Fin.ext
        change i.val + 1 = s + 2
        omega
      rw [hi, hj]
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        upperMiddleArray] using hv
    · let j : Fin s := ⟨i.val - 1, by have hib := i.isLt; omega⟩
      have hi : i.castSucc = splitEquiv s (.inr (.inl j.castSucc)) := by
        apply Fin.ext
        change i.val = i.val - 1 + 1
        omega
      have hj : i.succ = splitEquiv s (.inr (.inl j.succ)) := by
        apply Fin.ext
        change i.val + 1 = (i.val - 1 + 1) + 1
        omega
      rw [hi, hj]
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        upperMiddleArray] using hA j

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
