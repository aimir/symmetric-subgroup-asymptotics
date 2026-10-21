import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare3
open BinaryElementary16PhiZeroOuterCarries
private def masks : Fin 11 → ℕ := ![36902495346673844224,36902495346673844224,36902495346673844224,36902495346673844224,26388279132160,21990232621056,13194139598848,0,26388279132160,21990232621056,13194139598848]
def certificate : BinaryLinearConstraintCertificate input (target 3) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare3
