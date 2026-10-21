import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries

/-- Original retained input coefficient row 92; all 96 original columns. -/
theorem input_basis_row_92 : ∀ j : Fin 96,
    binaryRowFunctional (input 92) (Pi.single j 1) =
      inputActual 92 (Pi.single j 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
