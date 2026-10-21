import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare3
open BinaryRegular46FullConstantOuterCarries
private def masks : Fin 8 → ℕ := ![0,0,1099511627776,1099511627776,25068287289715295308283387904,25068287289715295308283387904,25068287289715296407795007488,25068287289715296407795007488]
def certificate : BinaryLinearConstraintCertificate input (target 3) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare3
