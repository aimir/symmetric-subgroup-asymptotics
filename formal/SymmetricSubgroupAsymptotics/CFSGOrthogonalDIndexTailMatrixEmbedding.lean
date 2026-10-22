import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
import SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual injective extension of a D tail matrix unit by the first
hyperbolic pair. Its coordinates and inverse matrices remain literal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDSerreMatrices CFSGMatrixIdentityExtension
variable (K : Type) [Field K]

def tailMatrixHom (n : ℕ) : Mat K n →* Mat K (n + 1) :=
  (Matrix.reindexAlgEquiv K K (tailEquiv n)).toMonoidHom.comp (extend K (Index n) (Fin 2))

def tailUnitHom (n : ℕ) : (Mat K n)ˣ →* (Mat K (n + 1))ˣ := Units.map (tailMatrixHom K n)

theorem tailMatrixHom_apply (n : ℕ) (A : Mat K n) (i j : Index (n + 1)) :
    tailMatrixHom K n A i j =
      Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K)
        ((tailEquiv n).symm i) ((tailEquiv n).symm j) := rfl

theorem tailMatrixHom_apply_equiv (n : ℕ) (A : Mat K n) (i j : Index n ⊕ Fin 2) :
    tailMatrixHom K n A (tailEquiv n i) (tailEquiv n j) =
      Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [tailMatrixHom_apply, (tailEquiv n).symm_apply_apply, (tailEquiv n).symm_apply_apply]

@[simp] theorem tailMatrixHom_tail_tail (n : ℕ) (A : Mat K n) (i j : Index n) :
    tailMatrixHom K n A (tailIndex n i) (tailIndex n j) = A i j := by
  rw [tailMatrixHom_apply, tailEquiv_symm_tailIndex, tailEquiv_symm_tailIndex]
  rfl

theorem tailMatrixHom_injective (n : ℕ) : Function.Injective (tailMatrixHom K n) := by
  intro A B h
  ext i j
  have he := congrArg (fun M : Mat K (n + 1) => M (tailIndex n i) (tailIndex n j)) h
  dsimp only at he
  simpa only [tailMatrixHom_tail_tail] using he

theorem tailUnitHom_injective (n : ℕ) : Function.Injective (tailUnitHom K n) := by
  intro A B h
  apply Units.ext
  apply tailMatrixHom_injective K n
  exact congrArg (fun u : (Mat K (n + 1))ˣ => (u : Mat K (n + 1))) h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailCoordinates
