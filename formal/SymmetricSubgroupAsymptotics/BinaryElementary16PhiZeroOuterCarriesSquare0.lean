import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare0
open BinaryElementary16PhiZeroOuterCarries
private def masks : Fin 11 → ℕ := ![167772161,274911461377,275045679104,33554433,0,0,0,0,0,0,0]
def certificate : BinaryLinearConstraintCertificate input (target 0) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare0
