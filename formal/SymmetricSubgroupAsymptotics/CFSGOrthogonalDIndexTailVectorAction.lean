import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailRootEmbedding
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The actual tail root embedding acts by the original smaller matrix
on all tail coordinates and fixes the SAME first hyperbolic coordinates.
The first hyperbolic pair is omitted and fixed exactly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

def tailRestriction (n : ℕ) (v : Index (n + 1) → K) : Index n → K := fun i => v (tailIndex n i)

theorem tailMatrixHom_mulVec_at_equiv (n : ℕ) (A : Mat K n) (v : Index (n + 1) → K)
    (x : Index n ⊕ Fin 2) :
    (tailMatrixHom K n A *ᵥ v) (tailEquiv n x) =
      (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ (v ∘ tailEquiv n)) x := by
  change (∑ j : Index (n + 1), tailMatrixHom K n A (tailEquiv n x) j * v j) =
    ∑ j : Index n ⊕ Fin 2, Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K) x j *
      v (tailEquiv n j)
  rw [← (tailEquiv n).sum_comp (fun j => tailMatrixHom K n A (tailEquiv n x) j * v j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [tailMatrixHom_apply_equiv]

theorem tailElementaryHom_tail_action (n : ℕ) (hn : 2 ≤ n) (g : elementaryRootGroup K n)
    (v : Index (n + 1) → K) :
    tailRestriction K n (((tailElementaryHom K n hn g).val : Mat K (n + 1)) *ᵥ v) =
      (g.val : Mat K n) *ᵥ tailRestriction K n v := by
  funext i
  change (tailMatrixHom K n (g.val : Mat K n) *ᵥ v) (tailEquiv n (Sum.inl i)) = _
  rw [tailMatrixHom_mulVec_at_equiv]
  simp [Matrix.fromBlocks_mulVec, tailRestriction, Function.comp_def] <;> rfl

theorem tailElementaryHom_head_positive (n : ℕ) (hn : 2 ≤ n) (g : elementaryRootGroup K n)
    (v : Index (n + 1) → K) :
    (((tailElementaryHom K n hn g).val : Mat K (n + 1)) *ᵥ v) (Sum.inl (0 : Fin (n + 1))) =
      v (Sum.inl (0 : Fin (n + 1))) := by
  change (tailMatrixHom K n (g.val : Mat K n) *ᵥ v) (tailEquiv n (Sum.inr 0)) = _
  rw [tailMatrixHom_mulVec_at_equiv]
  simp [Matrix.fromBlocks_mulVec, Function.comp_def]

theorem tailElementaryHom_head_negative (n : ℕ) (hn : 2 ≤ n) (g : elementaryRootGroup K n)
    (v : Index (n + 1) → K) :
    (((tailElementaryHom K n hn g).val : Mat K (n + 1)) *ᵥ v) (Sum.inr (0 : Fin (n + 1))) =
      v (Sum.inr (0 : Fin (n + 1))) := by
  change (tailMatrixHom K n (g.val : Mat K n) *ᵥ v) (tailEquiv n (Sum.inr 1)) = _
  rw [tailMatrixHom_mulVec_at_equiv]
  simp [Matrix.fromBlocks_mulVec, Function.comp_def]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
