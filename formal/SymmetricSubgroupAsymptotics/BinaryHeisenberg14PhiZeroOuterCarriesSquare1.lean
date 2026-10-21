import SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare1
open BinaryHeisenberg14PhiZeroOuterCarries
private def masks : Fin 10 → ℕ := ![264450,2,264450,0,0,0,0,0,0,0]
def certificate : BinaryLinearConstraintCertificate input (target 1) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryHeisenberg14PhiZeroOuterCarriesSquare1
