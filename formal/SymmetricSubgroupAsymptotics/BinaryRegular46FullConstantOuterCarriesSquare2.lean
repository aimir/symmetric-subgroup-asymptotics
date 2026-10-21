import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare2
open BinaryRegular46FullConstantOuterCarries
private def masks : Fin 8 → ℕ := ![19807116186506446277477138432,0,0,0,0,0,0,0]
def certificate : BinaryLinearConstraintCertificate input (target 2) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare2
