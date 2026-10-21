import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries

/-- Original nonzero input168: longest retained relator18, radical row0. -/
theorem input_basis_row_168 : ∀ j : Fin 96,
    binaryRowFunctional (input 168) (Pi.single j 1) =
      inputActual 168 (Pi.single j 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
