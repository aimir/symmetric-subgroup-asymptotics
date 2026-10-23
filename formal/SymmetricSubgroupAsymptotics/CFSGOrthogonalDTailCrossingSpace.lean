import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCrossingSpaces
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailVectorAction

/-! Actual tail identity extension transports the one-crossed positive
space to the successor crossed space. No determinant/component shortcut
is used, and the calculation remains valid in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDTailCrossingSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIsometryIndexCrossingSpaces
variable (K : Type) [Field K]

theorem tail_restriction_action (r : ℕ) (A : Mat K r) (v : Index (r + 1) → K) :
    tailRestriction K r (tailMatrixHom K r A *ᵥ v) = A *ᵥ tailRestriction K r v := by
  funext i
  change (tailMatrixHom K r A *ᵥ v) (tailEquiv r (Sum.inl i)) = _
  rw [tailMatrixHom_mulVec_at_equiv]
  simp [Matrix.fromBlocks_mulVec, tailRestriction, Function.comp_def] <;> rfl

theorem tail_negative_head (r : ℕ) (A : Mat K r) (v : Index (r + 1) → K) :
    (tailMatrixHom K r A *ᵥ v) (Sum.inr 0) = v (Sum.inr 0) := by
  change (tailMatrixHom K r A *ᵥ v) (tailEquiv r (Sum.inr 1)) = _
  rw [tailMatrixHom_mulVec_at_equiv]
  simp [Matrix.fromBlocks_mulVec, Function.comp_def]

theorem tail_maps_positive_to_crossing (r : ℕ) (j : Fin r) (A : Mat K r)
    (hA : ∀ v ∈ positiveSpace K r, A *ᵥ v ∈ crossingSpace K r j)
    (v : Index (r + 1) → K) (hv : v ∈ positiveSpace K (r + 1)) :
    tailMatrixHom K r A *ᵥ v ∈ crossingSpace K (r + 1) j.succ := by
  apply crossing_of_tail K r j
  · rw [tail_negative_head]
    exact hv 0
  · change tailRestriction K r (tailMatrixHom K r A *ᵥ v) ∈ crossingSpace K r j
    rw [tail_restriction_action]
    apply hA
    intro i
    exact hv i.succ

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDTailCrossingSpace
