import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockMatrices
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel

/-! Sparse operator transport for the literal last-pair block extension.
Every root parameter is retained, while no target root-subgroup membership
or fixed-group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockOperators
open CFSGOrthogonalDSerreMatrices CFSGTwistedDHyperbolicBlockCoordinates
open CFSGTwistedDHyperbolicBlockMatrices
variable (K : Type) [Field K]

def zeroBlockLinear (n : ℕ) : Mat K n →ₗ[K] Mat K (n + 1) where
  toFun A := Matrix.reindexAlgEquiv K K (blockEquiv n) (Matrix.fromBlocks A 0 0 0)
  map_add' A B := by
    change Matrix.reindexAlgEquiv K K (blockEquiv n) (Matrix.fromBlocks (A + B) 0 0 0) =
      Matrix.reindexAlgEquiv K K (blockEquiv n) (Matrix.fromBlocks A 0 0 0) +
        Matrix.reindexAlgEquiv K K (blockEquiv n) (Matrix.fromBlocks B 0 0 0)
    rw [← map_add]
    congr 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_smul' a A := by
    change Matrix.reindexAlgEquiv K K (blockEquiv n) (Matrix.fromBlocks (a • A) 0 0 0) = _
    rw [← map_smul]
    congr 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]

theorem zeroBlockLinear_apply_equiv (n : ℕ) (A : Mat K n) (i j : Index n ⊕ Fin 2) :
    zeroBlockLinear K n A (blockEquiv n i) (blockEquiv n j) = Matrix.fromBlocks A 0 0 0 i j := by
  change Matrix.fromBlocks A 0 0 0 ((blockEquiv n).symm (blockEquiv n i))
    ((blockEquiv n).symm (blockEquiv n j)) = _
  rw [(blockEquiv n).symm_apply_apply, (blockEquiv n).symm_apply_apply]

private theorem blockIndex_ne_extra (n : ℕ) (i : Index n) (j : Fin 2) :
    blockIndex n i ≠ blockEquiv n (Sum.inr j) := by
  intro h
  have hh : blockEquiv n (Sum.inl i) = blockEquiv n (Sum.inr j) := h
  cases (blockEquiv n).injective hh

private theorem extra_ne_blockIndex (n : ℕ) (j : Fin 2) (i : Index n) :
    blockEquiv n (Sum.inr j) ≠ blockIndex n i := Ne.symm (blockIndex_ne_extra n i j)

theorem zeroBlockLinear_single (n : ℕ) (i j : Index n) (a : K) :
    zeroBlockLinear K n (Matrix.single i j a) = Matrix.single (blockIndex n i) (blockIndex n j) a := by
  ext x y
  obtain ⟨x, rfl⟩ := (blockEquiv n).surjective x
  obtain ⟨y, rfl⟩ := (blockEquiv n).surjective y
  rw [zeroBlockLinear_apply_equiv]
  change Matrix.fromBlocks (Matrix.single i j a) 0 0 0 x y =
    Matrix.single (blockEquiv n (Sum.inl i)) (blockEquiv n (Sum.inl j)) a
      (blockEquiv n x) (blockEquiv n y)
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.single_apply, (blockIndex_injective n).eq_iff,
      blockIndex_ne_extra, extra_ne_blockIndex]

theorem zeroBlockLinear_transpose (n : ℕ) (A : Mat K n) :
    zeroBlockLinear K n A.transpose = (zeroBlockLinear K n A).transpose := by
  ext x y
  obtain ⟨x, rfl⟩ := (blockEquiv n).surjective x
  obtain ⟨y, rfl⟩ := (blockEquiv n).surjective y
  simp only [Matrix.transpose_apply, zeroBlockLinear_apply_equiv]
  cases x <;> cases y <;> rfl

theorem blockMatrixHom_eq_one_add (n : ℕ) (A : Mat K n) :
    blockMatrixHom K n A = 1 + zeroBlockLinear K n (A - 1) := by
  ext x y
  obtain ⟨x, rfl⟩ := (blockEquiv n).surjective x
  obtain ⟨y, rfl⟩ := (blockEquiv n).surjective y
  rw [blockMatrixHom_apply_equiv, Matrix.add_apply, zeroBlockLinear_apply_equiv]
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, (blockIndex_injective n).eq_iff,
      blockIndex_ne_extra, extra_ne_blockIndex] <;> abel

theorem blockUnitHom_root_val (n : ℕ) (neg : Bool) (i : Fin n) (a : K) :
    (blockUnitHom K n (rootTransvection K n neg i a) : Mat K (n + 1)) =
      1 + a • zeroBlockLinear K n (rootMatrix K n neg i) := by
  change blockMatrixHom K n (rootTransvection K n neg i a : Mat K n) = _
  rw [blockMatrixHom_eq_one_add, rootTransvection_val, add_sub_cancel_left, map_smul]

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockOperators
