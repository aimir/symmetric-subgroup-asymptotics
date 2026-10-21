import SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare2
open BinaryElementary16PhiZeroOuterCarries
private def masks : Fin 11 → ℕ := ![18014398509481984,0,18014398509481984,0,15032385536,0,15032385536,10737420288,4294967296,10737420288,4294967296]
def certificate : BinaryLinearConstraintCertificate input (target 2) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarriesSquare2
