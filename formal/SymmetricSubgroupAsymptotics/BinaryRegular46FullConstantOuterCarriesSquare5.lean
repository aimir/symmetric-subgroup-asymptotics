import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare5
open BinaryRegular46FullConstantOuterCarries
private def masks : Fin 8 → ℕ := ![0,20307169614838937244742276087808,20307168404437378117410458959872,1210401559162516188168192,0,20307169614838937244742276087808,20307168404437378117410458959872,1210401559162516188168192]
def certificate : BinaryLinearConstraintCertificate input (target 5) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare5
