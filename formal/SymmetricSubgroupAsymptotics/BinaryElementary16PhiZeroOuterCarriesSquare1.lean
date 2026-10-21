import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare1
open BinaryElementary16PhiZeroOuterCarries
private def masks : Fin 11 → ℕ := ![0,9007199254740992,9007199254740992,0,0,7340032,7340032,6291584,6291584,1048576,1048576]
def certificate : BinaryLinearConstraintCertificate input (target 1) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare1
