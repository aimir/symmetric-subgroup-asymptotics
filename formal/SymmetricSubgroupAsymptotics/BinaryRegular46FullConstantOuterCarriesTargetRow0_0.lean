import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries

/-- Original square 0, denominator row 0; all 96 original columns. -/
theorem target_basis_row_0_0 : ∀ k : Fin 96,
    binaryRowFunctional (target 0 0) (Pi.single k 1) =
      targetActual 0 0 (Pi.single k 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
