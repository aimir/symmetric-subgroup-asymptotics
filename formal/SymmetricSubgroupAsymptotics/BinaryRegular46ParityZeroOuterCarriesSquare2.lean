import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare2
open BinaryRegular46ParityZeroOuterCarries
private def masks : Fin 12 → ℕ := ![166154292064224643496070339270607104,0,166154291754739630215960756725285120,309485015585952591759081472,0,0,0,0,0,0,0,0]
def certificate : BinaryLinearConstraintCertificate input
    (fun j : Fin 12 => target ⟨24 + j.val, by omega⟩) where
  support j := Finset.univ.filter fun i => (masks j).testBit i.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare2
