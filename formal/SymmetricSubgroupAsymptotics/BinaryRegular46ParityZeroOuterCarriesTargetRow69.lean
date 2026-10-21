import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries

/-- Original retained target coefficient row 69; all 96 original columns. -/
theorem target_basis_row_69 : ∀ k : Fin 96,
    binaryRowFunctional (target 69) (Pi.single k 1) =
      targetActual 69 (Pi.single k 1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarries
