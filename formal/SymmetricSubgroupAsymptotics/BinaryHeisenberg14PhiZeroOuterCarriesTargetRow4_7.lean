import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries

/-- Original square 4, denominator row 7; all 96 original columns. -/
theorem target_basis_row_4_7 : ∀ k : Fin 96,
    binaryRowFunctional (target 4 7) (Pi.single k 1) =
      targetActual 4 7 (Pi.single k 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries
