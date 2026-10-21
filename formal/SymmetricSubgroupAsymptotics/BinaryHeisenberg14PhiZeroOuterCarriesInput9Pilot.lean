import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries

/-- Exact original coefficient row 9, with all 96 offset basis columns. -/
theorem input_basis_row_9 : ∀ j : Fin 96,
    binaryRowFunctional (input 9) (Pi.single j 1) =
      inputActual 9 (Pi.single j 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarries
