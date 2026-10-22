import SymmetricSubgroupAsymptotics.CFSGAlternatingMatrixParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexShears

/-! Actual membership for an arbitrary alternating paired-coordinate
shear in the SAME original B elementary subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBArbitraryShearMembership
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexShears CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem upper_mem (h2 : (2 : K) ≠ 0) (s : ℕ)
    (B : Matrix (Fin (s + 1)) (Fin (s + 1)) K)
    (ht : B.transpose = -B) (hd : ∀ i, B i i = 0) :
    extensionHom K (s + 1) (upper B) ∈ elementaryRootGroup K (s + 1) := by
  rw [← CFSGAlternatingMatrixParameters.alternating_parametersOf (s + 1) B ht hd]
  exact upper_alternating_mem K h2 s _

theorem lower_mem (h2 : (2 : K) ≠ 0) (s : ℕ)
    (B : Matrix (Fin (s + 1)) (Fin (s + 1)) K)
    (ht : B.transpose = -B) (hd : ∀ i, B i i = 0) :
    extensionHom K (s + 1) (lower B) ∈ elementaryRootGroup K (s + 1) := by
  rw [← CFSGAlternatingMatrixParameters.alternating_parametersOf (s + 1) B ht hd]
  exact lower_alternating_mem K h2 s _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBArbitraryShearMembership
