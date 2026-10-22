import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockCoordinates
import SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual matrix-unit extension fixing the final hyperbolic pair.
This file proves the literal block action and injectivity only; root
membership in the original Derived preimage is a separate obligation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockMatrices
open CFSGOrthogonalDSerreMatrices CFSGTwistedDHyperbolicBlockCoordinates
open CFSGMatrixIdentityExtension
variable (K : Type) [Field K]

def blockMatrixHom (n : ℕ) : Mat K n →* Mat K (n + 1) :=
  (Matrix.reindexAlgEquiv K K (blockEquiv n)).toMonoidHom.comp (extend K (Index n) (Fin 2))

def blockUnitHom (n : ℕ) : (Mat K n)ˣ →* (Mat K (n + 1))ˣ :=
  Units.map (blockMatrixHom K n)

theorem blockMatrixHom_apply (n : ℕ) (A : Mat K n) (i j : Index (n + 1)) :
    blockMatrixHom K n A i j =
      Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K)
        ((blockEquiv n).symm i) ((blockEquiv n).symm j) := rfl

theorem blockMatrixHom_apply_equiv (n : ℕ) (A : Mat K n) (i j : Index n ⊕ Fin 2) :
    blockMatrixHom K n A (blockEquiv n i) (blockEquiv n j) =
      Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [blockMatrixHom_apply, (blockEquiv n).symm_apply_apply, (blockEquiv n).symm_apply_apply]

@[simp] theorem blockMatrixHom_block_block (n : ℕ) (A : Mat K n) (i j : Index n) :
    blockMatrixHom K n A (blockIndex n i) (blockIndex n j) = A i j := by
  rw [blockMatrixHom_apply, blockEquiv_symm_blockIndex, blockEquiv_symm_blockIndex]
  rfl

theorem blockMatrixHom_injective (n : ℕ) : Function.Injective (blockMatrixHom K n) := by
  intro A B h
  ext i j
  have he := congrArg (fun M : Mat K (n + 1) => M (blockIndex n i) (blockIndex n j)) h
  dsimp only at he
  simpa only [blockMatrixHom_block_block] using he

theorem blockUnitHom_injective (n : ℕ) : Function.Injective (blockUnitHom K n) := by
  intro A B h
  apply Units.ext
  apply blockMatrixHom_injective K n
  exact congrArg (fun u : (Mat K (n + 1))ˣ => (u : Mat K (n + 1))) h

theorem blockMatrixHom_action (n : ℕ) (A : Mat K n) (v : Index (n + 1) → K) :
    (blockMatrixHom K n A *ᵥ v) ∘ blockIndex n = A *ᵥ (v ∘ blockIndex n) := by
  change ((Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K)).submatrix
    (blockEquiv n).symm (blockEquiv n).symm *ᵥ v) ∘ blockIndex n = _
  rw [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  funext i
  simp only [Function.comp_apply, blockEquiv_symm_blockIndex, Sum.elim_inl,
    Matrix.zero_mulVec, add_zero]
  rfl

theorem blockMatrixHom_positive_last (n : ℕ) (A : Mat K n) (v : Index (n + 1) → K) :
    (blockMatrixHom K n A *ᵥ v) (Sum.inl (Fin.last n)) = v (Sum.inl (Fin.last n)) := by
  change ((Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K)).submatrix
    (blockEquiv n).symm (blockEquiv n).symm *ᵥ v) (Sum.inl (Fin.last n)) = _
  rw [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_apply, blockEquiv_symm_positive_last, Sum.elim_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, Equiv.symm_symm, blockEquiv_zero]

theorem blockMatrixHom_negative_last (n : ℕ) (A : Mat K n) (v : Index (n + 1) → K) :
    (blockMatrixHom K n A *ᵥ v) (Sum.inr (Fin.last n)) = v (Sum.inr (Fin.last n)) := by
  change ((Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K)).submatrix
    (blockEquiv n).symm (blockEquiv n).symm *ᵥ v) (Sum.inr (Fin.last n)) = _
  rw [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_apply, blockEquiv_symm_negative_last, Sum.elim_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, Equiv.symm_symm, blockEquiv_one]

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockMatrices
