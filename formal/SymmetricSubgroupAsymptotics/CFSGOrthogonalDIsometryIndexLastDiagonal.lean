import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexLastSquares
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentMatrices

/-! Literal paired GL lifts fix the actual positive subspace, hence
belong to the genuine even component. The remaining determinant
parameter therefore defines a homomorphism into that SAME component. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexLastDiagonal
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexComponentMatrices
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIsometryIndexGeneralLinearLift CFSGOrthogonalDIsometryIndexLastSquares
variable (K : Type) [Field K]

theorem generalLinearLift_positive_fixed (r : ℕ) (A : Matrix.GeneralLinearGroup (Fin r) K) :
    (positiveSpace K r).map (ambientLinearEquiv K r (generalLinearLift K r A)).toLinearMap =
      positiveSpace K r := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro x ⟨v, hv, rfl⟩ i
    have hz : v ∘ Sum.inr = (0 : Fin r → K) := funext hv
    change (Matrix.fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).transpose *ᵥ v)
        (Sum.inr i) = 0
    rw [Matrix.fromBlocks_mulVec]
    change (((0 : Matrix (Fin r) (Fin r) K) *ᵥ (v ∘ Sum.inl) +
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).transpose *ᵥ
        (v ∘ Sum.inr)) : Fin r → K) i = 0
    rw [hz, Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]
    rfl
  · rw [(ambientLinearEquiv K r (generalLinearLift K r A)).finrank_map_eq]

theorem generalLinearLift_mem_component (r : ℕ) (A : Matrix.GeneralLinearGroup (Fin r) K) :
    generalLinearLift K r A ∈ componentMatrices K r := by
  apply mem_componentMatrices_of_positive_fixed K r
  · intro x
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
    exact generalLinearLift_preserves K r A x
  · exact generalLinearLift_positive_fixed K r A

def lastComponentHom (s : ℕ) : Kˣ →* componentMatrices K (s + 1) :=
  (lastDiagonalHom K s).codRestrict (componentMatrices K (s + 1)) (fun a => by
    rw [lastDiagonalHom_eq_lift]
    exact generalLinearLift_mem_component K (s + 1) _)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexLastDiagonal
