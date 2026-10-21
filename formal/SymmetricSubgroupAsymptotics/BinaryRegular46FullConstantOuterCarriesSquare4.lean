import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare4
open BinaryRegular46FullConstantOuterCarries
private def masks : Fin 8 → ℕ := ![0,281474976710656,0,281474976710656,79228162514264619068520660992,79228162514264337593544015872,79228162514264619068520660992,79228162514264337593544015872]
def certificate : BinaryLinearConstraintCertificate input (target 4) where
  support j := Finset.univ.filter fun k => (masks j).testBit k.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesSquare4
