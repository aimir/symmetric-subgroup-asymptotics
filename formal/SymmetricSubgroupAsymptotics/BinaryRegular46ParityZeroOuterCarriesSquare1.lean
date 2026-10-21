import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesDefinitions
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare1
open BinaryRegular46ParityZeroOuterCarries
private def masks : Fin 12 → ℕ := ![166153737467162598049824160035635201,166153737157602030365597601917566976,0,309560567685915407978332417,0,0,0,0,0,0,0,0]
def certificate : BinaryLinearConstraintCertificate input
    (fun j : Fin 12 => target ⟨12 + j.val, by omega⟩) where
  support j := Finset.univ.filter fun i => (masks j).testBit i.val
  target_eq := by decide +kernel
end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesSquare1
