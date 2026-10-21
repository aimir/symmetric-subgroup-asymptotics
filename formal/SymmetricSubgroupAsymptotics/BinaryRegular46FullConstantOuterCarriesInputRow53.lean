import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries

/-- Original retained input coefficient row 53; all 96 original columns. -/
theorem input_basis_row_53 : ∀ j : Fin 96,
    binaryRowFunctional (input 53) (Pi.single j 1) =
      inputActual 53 (Pi.single j 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
