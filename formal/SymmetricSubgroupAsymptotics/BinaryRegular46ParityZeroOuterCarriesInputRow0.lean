import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries

/-- Original retained input coefficient row 0; all 96 original columns. -/
theorem input_basis_row_0 : ∀ j : Fin 96,
    binaryRowFunctional (input 0) (Pi.single j 1) =
      inputActual 0 (Pi.single j 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries
