import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries

/-- Original square 5, denominator row 5; all 96 original columns. -/
theorem target_basis_row_5_5 : ∀ k : Fin 96,
    binaryRowFunctional (target 5 5) (Pi.single k 1) =
      targetActual 5 5 (Pi.single k 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
