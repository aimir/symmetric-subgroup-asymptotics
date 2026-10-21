import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries

/-- Original square 1, denominator row 8; all 96 original columns. -/
theorem target_basis_row_1_8 : ∀ k : Fin 96,
    binaryRowFunctional (target 1 8) (Pi.single k 1) =
      targetActual 1 8 (Pi.single k 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries
