import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailMatrixEmbedding
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

/-! Literal D tail root operators extend to their successor-index
operators. The real guard n>=2 is retained: the rank-one terminal D
matrix is zero and cannot be silently identified with a rank-two fork. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

def zeroTailLinear (n : ℕ) : Mat K n →ₗ[K] Mat K (n + 1) where
  toFun A := Matrix.reindexAlgEquiv K K (tailEquiv n) (Matrix.fromBlocks A 0 0 0)
  map_add' A B := by
    change Matrix.reindexAlgEquiv K K (tailEquiv n) (Matrix.fromBlocks (A + B) 0 0 0) =
      Matrix.reindexAlgEquiv K K (tailEquiv n) (Matrix.fromBlocks A 0 0 0) +
        Matrix.reindexAlgEquiv K K (tailEquiv n) (Matrix.fromBlocks B 0 0 0)
    rw [← map_add]
    congr 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_smul' a A := by
    change Matrix.reindexAlgEquiv K K (tailEquiv n) (Matrix.fromBlocks (a • A) 0 0 0) = _
    rw [← map_smul]
    congr 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]

theorem zeroTailLinear_apply_equiv (n : ℕ) (A : Mat K n) (i j : Index n ⊕ Fin 2) :
    zeroTailLinear K n A (tailEquiv n i) (tailEquiv n j) = Matrix.fromBlocks A 0 0 0 i j := by
  change Matrix.fromBlocks A 0 0 0 ((tailEquiv n).symm (tailEquiv n i))
    ((tailEquiv n).symm (tailEquiv n j)) = _
  rw [(tailEquiv n).symm_apply_apply, (tailEquiv n).symm_apply_apply]

private theorem tailIndex_ne_head (n : ℕ) (i : Index n) (j : Fin 2) :
    tailIndex n i ≠ tailEquiv n (Sum.inr j) := by
  intro h
  have hh : tailEquiv n (Sum.inl i) = tailEquiv n (Sum.inr j) := h
  cases (tailEquiv n).injective hh

private theorem head_ne_tailIndex (n : ℕ) (j : Fin 2) (i : Index n) :
    tailEquiv n (Sum.inr j) ≠ tailIndex n i := Ne.symm (tailIndex_ne_head n i j)

theorem zeroTailLinear_single (n : ℕ) (i j : Index n) (a : K) :
    zeroTailLinear K n (Matrix.single i j a) = Matrix.single (tailIndex n i) (tailIndex n j) a := by
  ext x y
  obtain ⟨x, rfl⟩ := (tailEquiv n).surjective x
  obtain ⟨y, rfl⟩ := (tailEquiv n).surjective y
  rw [zeroTailLinear_apply_equiv]
  change Matrix.fromBlocks (Matrix.single i j a) 0 0 0 x y =
    Matrix.single (tailEquiv n (Sum.inl i)) (tailEquiv n (Sum.inl j)) a (tailEquiv n x) (tailEquiv n y)
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.single_apply, (tailIndex_injective n).eq_iff,
      tailIndex_ne_head, head_ne_tailIndex]

theorem zeroTailLinear_transpose (n : ℕ) (A : Mat K n) :
    zeroTailLinear K n A.transpose = (zeroTailLinear K n A).transpose := by
  ext x y
  obtain ⟨x, rfl⟩ := (tailEquiv n).surjective x
  obtain ⟨y, rfl⟩ := (tailEquiv n).surjective y
  simp only [Matrix.transpose_apply, zeroTailLinear_apply_equiv]
  cases x <;> cases y <;> rfl

theorem tailMatrixHom_eq_one_add (n : ℕ) (A : Mat K n) :
    tailMatrixHom K n A = 1 + zeroTailLinear K n (A - 1) := by
  ext x y
  obtain ⟨x, rfl⟩ := (tailEquiv n).surjective x
  obtain ⟨y, rfl⟩ := (tailEquiv n).surjective y
  rw [tailMatrixHom_apply_equiv, Matrix.add_apply, zeroTailLinear_apply_equiv]
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, (tailIndex_injective n).eq_iff,
      tailIndex_ne_head, head_ne_tailIndex] <;> abel

theorem zeroTailLinear_positive (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    zeroTailLinear K n (positive K n i) = positive K (n + 1) i.succ := by
  by_cases hi : i.val + 1 < n
  · have hi' : i.succ.val + 1 < n + 1 := by simp only [Fin.val_succ]; omega
    rw [positive, dif_pos hi, positive, dif_pos hi', map_sub,
      zeroTailLinear_single, zeroTailLinear_single]
    rfl
  · have hi' : ¬i.succ.val + 1 < n + 1 := by simp only [Fin.val_succ]; omega
    have hp : previous (n + 1) i.succ = (previous n i).succ := by
      apply Fin.ext
      change i.val + 1 - 1 = i.val - 1 + 1
      have hb := i.isLt
      omega
    rw [positive, dif_neg hi, positive, dif_neg hi', map_sub,
      zeroTailLinear_single, zeroTailLinear_single, hp]
    rfl

theorem zeroTailLinear_negative (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    zeroTailLinear K n (negative K n i) = negative K (n + 1) i.succ := by
  change zeroTailLinear K n (positive K n i).transpose = (positive K (n + 1) i.succ).transpose
  rw [zeroTailLinear_transpose, zeroTailLinear_positive K n hn i]

theorem zeroTailLinear_rootMatrix (n : ℕ) (hn : 2 ≤ n) (neg : Bool) (i : Fin n) :
    zeroTailLinear K n (rootMatrix K n neg i) = rootMatrix K (n + 1) neg i.succ := by
  cases neg
  · simpa only [rootMatrix, Bool.false_eq_true, if_false] using zeroTailLinear_positive K n hn i
  · simpa only [rootMatrix, if_true] using zeroTailLinear_negative K n hn i

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
