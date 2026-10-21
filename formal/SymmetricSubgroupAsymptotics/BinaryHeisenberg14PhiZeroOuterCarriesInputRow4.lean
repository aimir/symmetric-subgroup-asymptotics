import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries

/-- Original retained input coefficient row 4; all 96 original columns. -/
theorem input_basis_row_4 : ∀ j : Fin 96,
    binaryRowFunctional (input 4) (Pi.single j 1) =
      inputActual 4 (Pi.single j 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries
